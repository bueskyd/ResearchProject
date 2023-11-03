module AutoCPS (plugin) where

import Control.Monad (forM_, join, mapAndUnzipM, unless, void, when)
import Data.Data
import qualified Data.Foldable
import Data.Maybe (fromMaybe)
import Data.Typeable
import Debug.Trace
import GHC.Builtin.Types (manyDataConTy)
import GHC.Core.TyCo.Rep
import GHC.Plugins
import GHC.Types.Id.Info (vanillaIdInfo)
import GHC.Types.Unique (mkLocalUnique)
import GHC.Types.Var

data PrintOptions = PrintOptions {indentation :: Int, indentationString :: String}

incInden :: PrintOptions -> PrintOptions
incInden printOptions = PrintOptions (indentation printOptions + 1) (indentationString printOptions)

makeIndentation :: PrintOptions -> String
makeIndentation printOptions =
  Control.Monad.join (replicate (indentation printOptions) (indentationString printOptions))

plugin :: Plugin
plugin =
    defaultPlugin
        { installCoreToDos = install
        }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = return (CoreDoPluginPass "Hi mom" pass : todo)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
    dflags <- getDynFlags
    bindsOnlyPass (mapM (printBind dflags)) guts
    where
        printOptions = PrintOptions 0 " - "
        {-autoCPS :: DynFlags -> CoreBind -> CoreBndr -> Expr CoreBndr -> CoreM (CoreBndr, Expr CoreBndr)
        autoCPS dflags bind bndr expr = do
        anns <- annotationsOn guts bndr :: CoreM [String]
        cps <- transformToCPS dflags bind

        case (bind, cps) of
            (Rec lst0, Rec lst1) -> do
            putMsgS "Original"
            printAbsyn dflags printOptions $ snd $ head lst0
            --putMsgS $ showSDoc dflags (ppr $ snd $ head lst0)
            putMsgS "Transformed to CPS"
            printAbsyn dflags printOptions $ snd $ head lst1
            --putMsgS $ showSDoc dflags (ppr $ snd $ head lst1)
            _ -> return ()
        when ("AUTO_CPS" `elem` anns) $ do
            putMsgS ("Tail recursive: " ++ show (isTailRecursive dflags bind))
            putMsgS (showSDoc dflags (ppr bind))
            printAbsyns dflags printOptions [(bndr, expr)]
            putMsgS ""
        return (bndr,expr)-}
        printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags bind = do
            cps <- transformToCPS dflags bind
            {-case bind of
                NonRec bndr expr -> do
                    putMsgS $ showSDoc dflags $ ppr bndr
                    putMsgS $ showSDoc dflags $ ppr expr
                Rec lst -> do
                    _ <- sequence $ map (\(bndr, expr) -> do
                        putMsgS $ showSDoc dflags $ ppr bndr
                        putMsgS $ showSDoc dflags $ ppr expr) lst
                    return ()-}
            case (bind, cps) of
                (Rec lst0, Rec lst1) -> do
                    putMsgS "Original"
                    -- printAbsyn dflags printOptions $ snd $ head lst0
                    putMsgS $ showSDoc dflags (ppr $ fst $ head lst0)
                    putMsgS $ showSDoc dflags (ppr $ snd $ head lst0)
                    putMsgS "Transformed to CPS"
                    -- printAbsyn dflags printOptions $ snd $ head lst1
                    putMsgS $ showSDoc dflags (ppr $ fst $ head lst1)
                    putMsgS $ showSDoc dflags (ppr $ snd $ head lst1)

                    putMsgS "Test"
                    (expr', newBindings) <- replaceNonTailCalls dflags (snd $ head lst0) (fst $ head lst0)
                    putMsgS $ showSDoc dflags (ppr expr')
                    putMsgS $ "Calls replaced: " ++ show (length newBindings)
                    mapM_ (putMsgS . showSDoc dflags . ppr) newBindings
                _ -> return ()
            return cps

transformToCPS :: DynFlags -> CoreBind -> CoreM CoreBind
transformToCPS dflags (NonRec coreBndr expr) = return $ NonRec coreBndr expr -- Deal with this later
transformToCPS dflags (Rec lst) = do
    transformedFunctions <- mapM transformToCPS' lst
    return $ Rec transformedFunctions
    where
        transformToCPS' :: (CoreBndr, CoreExpr) -> CoreM (CoreBndr, CoreExpr)
        transformToCPS' (coreBndr, expr) = do
            localCoreBndr <- makeLocalCPSFun dflags coreBndr
            transformedBody <- transformBodyToCPS dflags (coreBndr, expr) localCoreBndr
            localTailRecursive <- wrapCPS (coreBndr, expr) (localCoreBndr, transformedBody)
            return (coreBndr, localTailRecursive)

transformBodyToCPS :: DynFlags -> (CoreBndr, CoreExpr) -> CoreBndr -> CoreM CoreExpr
transformBodyToCPS dflags (coreBndr, expr) localCoreBndr = do
    let coreBndrName = getCoreBndrName dflags coreBndr
    let continuationType = makeContinuationType coreBndr
    continuation <- makeVar "cont" continuationType
    case prependArg expr continuation of
        Nothing -> return expr -- expr is not a lambda
        Just expr' -> do
            semiTransformedBody <- transformBodyToCPS' coreBndr expr' continuation [coreBndrName]
            let transformedBody = replaceRecursiveCalls dflags semiTransformedBody coreBndrName localCoreBndr
            return transformedBody
    where
        transformBodyToCPS' coreBndr expr continuation coreBndrNames = aux expr coreBndrNames True
            where
                aux expr coreBndrNames inTailPosition = case expr of
                    (Var id) -> return $ Var id
                    (Lit lit) -> return $ Lit lit
                    (App expr0 expr1) -> do
                        (exprWithBindings, newBindings) <- replaceNonTailCalls dflags (App expr0 expr1) coreBndr
                        if not (null newBindings) || inTailPosition
                        then
                            let combiningCall = App (Var continuation) exprWithBindings
                                tailRecExpr = foldl (\acc (coreBndr, coreExpr) -> App coreExpr $ Lam coreBndr acc) combiningCall newBindings
                            in return tailRecExpr
                        else return $ App expr0 expr1
                    (Lam lamCoreBndr expr) -> do
                        expr' <- aux expr coreBndrNames True
                        return $ Lam lamCoreBndr expr'
                    (Let (NonRec bndr expr0) expr1) -> do
                        let localCoreBndrName = getCoreBndrName dflags bndr
                        expr0' <- aux expr0 (localCoreBndrName : coreBndrNames) True
                        expr1' <- aux expr1 (localCoreBndrName : coreBndrNames) inTailPosition
                        return $ Let (NonRec bndr expr0') expr1'
                    (Let (Rec lst) expr) -> do
                        lst' <- mapM
                            ( \(localCoreBndr, expr) -> do
                                let localCoreBndrName = getCoreBndrName dflags localCoreBndr
                                expr' <- aux expr (localCoreBndrName : coreBndrNames) True
                                return (localCoreBndr, expr')
                            )
                            lst
                        expr' <- aux expr coreBndrNames inTailPosition
                        return $ Let (Rec lst') expr'
                    (Case expr caseCoreBndr typ alternatives) -> do
                        altAsCPS <- mapM
                            ( \(Alt altCon coreBndrs rhs) -> do
                                -- if containsCallToAny dflags rhs coreBndrNames then do
                                rhs' <- aux rhs coreBndrNames inTailPosition
                                return $ Alt altCon coreBndrs rhs'
                                {-else do
                                let application = App (Var continuation) rhs
                                return $ Alt altCon coreBndrs application-}
                            )
                            alternatives
                        expr' <- aux expr coreBndrNames False
                        return $ Case expr' caseCoreBndr typ altAsCPS
                    (Cast expr coercion) -> do
                        expr' <- aux expr coreBndrNames False
                        return $ Cast expr' coercion
                    (Tick tickish expr) -> do
                        expr' <- aux expr coreBndrNames False -- No idea if inTailPosition should actually be False
                        return $ Tick tickish expr'
                    (Type typ) -> return $ Type typ
                    (Coercion coercion) -> return $ Coercion coercion

replaceRecursiveCalls :: DynFlags -> CoreExpr -> String -> Var -> CoreExpr
replaceRecursiveCalls dflags expr target result = aux expr where
    aux expr = case expr of
        (Var id) ->
            let varName = getCoreBndrName dflags id
            in if varName == target
                then Var result
                else Var id
        (Lit lit) -> Lit lit
        (App expr0 expr1) ->
            let expr0' = aux expr0
                expr1' = aux expr1
            in App expr0' expr1'
        (Lam lamCoreBndr expr) ->
            let expr' = aux expr
            in Lam lamCoreBndr expr'
        (Let (NonRec bndr expr0) expr1) ->
            let expr0' = aux expr0
                expr1' = aux expr1
            in Let (NonRec bndr expr0') expr1'
        (Let (Rec lst) expr) -> let
            lst' = map
                (\(localCoreBndr, expr) -> let
                    localCoreBndrName = getCoreBndrName dflags localCoreBndr
                    expr' = aux expr
                    in (localCoreBndr, expr')) lst
            expr' = aux expr
            in Let (Rec lst') expr'
        (Case expr caseCoreBndr typ alternatives) -> let
            altAsCPS = map
                    (\(Alt altCon coreBndrs rhs) ->
                        let rhs' = aux rhs
                        in Alt altCon coreBndrs rhs')
                    alternatives
            expr' = aux expr
            in Case expr' caseCoreBndr typ altAsCPS
        (Cast expr coercion) -> let
            expr' = aux expr
            in Cast expr' coercion
        (Tick tickish expr) -> let
            expr' = aux expr
            in Tick tickish expr'
        (Type typ) -> Type typ
        (Coercion coercion) -> Coercion coercion

replaceNonTailCalls :: DynFlags -> CoreExpr -> CoreBndr -> CoreM (CoreExpr, [(CoreBndr, CoreExpr)])
replaceNonTailCalls dflags expr coreBndr = aux expr where
    aux :: CoreExpr -> CoreM (CoreExpr, [(CoreBndr, CoreExpr)])
    aux expr = case expr of
        (Var id) -> return (Var id, [])
        (Lit lit) -> return (Lit lit, [])
        (App expr0 expr1) -> do
            (expr0', newBindings0) <- aux expr0
            (expr1', newBindings1) <- aux expr1
            case getReturnType coreBndr of
                Nothing -> return (expr0', newBindings0) -- Should never happen
                Just returnType ->
                    if isCallTo dflags expr1' (getCoreBndrName dflags coreBndr)
                    then do
                        newBindingName <- makeVar "contBndr" returnType
                        return (App expr0' (Var newBindingName), (newBindingName, expr1') : newBindings0 ++ newBindings1)
                    else return (App expr0' expr1', newBindings0 ++ newBindings1)
        (Lam lamCoreBndr expr) -> do
            (expr', newBindings) <- aux expr
            return (Lam lamCoreBndr expr', newBindings)
        (Let (NonRec bndr expr0) expr1) -> do
            (expr0', newBindings0) <- aux expr0
            (expr1', newBindings1) <- aux expr1
            return (Let (NonRec bndr expr0') expr1', newBindings0 ++ newBindings1)
        (Let (Rec lst) expr) -> do
            (lst', newBindings0) <- mapAndUnzipM
                (\(localCoreBndr, expr) -> do
                    (expr', bindings) <- aux expr
                    return ((localCoreBndr, expr'), bindings))
                lst
            (expr', newBindings1) <- aux expr
            return (Let (Rec lst') expr', join newBindings0 ++ newBindings1)
        (Case expr caseCoreBndr typ alternatives) -> do
            (altAsCPS, newBindings0) <- mapAndUnzipM
                (\(Alt altCon coreBndrs rhs) -> do
                    (rhs', bindings) <- aux rhs
                    return (Alt altCon coreBndrs rhs', bindings))
                alternatives
            (expr', newBindings1) <- aux expr
            return (Case expr' caseCoreBndr typ altAsCPS, join newBindings0 ++ newBindings1)
        (Cast expr coercion) -> do
            (expr', newBindings) <- aux expr
            return (Cast expr' coercion, newBindings)
        (Tick tickish expr) -> do
            (expr', newBindings) <- aux expr
            return (Tick tickish expr', newBindings)
        (Type typ) -> return (Type typ, [])
        (Coercion coercion) -> return (Coercion coercion, [])

mkIdentity :: Type -> CoreM CoreExpr
mkIdentity typ = do
    unique <- getUniqueM
    let varName = mkSystemVarName unique (mkFastString "identity")
    let var = mkLocalVar VanillaId varName Many typ vanillaIdInfo
    return $ mkCoreLams [var] (Var var)

wrapCPS :: (CoreBndr, CoreExpr) -> (CoreBndr, CoreExpr) -> CoreM CoreExpr
wrapCPS (originalCoreBndr, originalExpr) (cpsCoreBndr, cpsExpr) = do
    let (args, _) = collectBinders originalExpr
    case getReturnType originalCoreBndr of
        Nothing -> return originalExpr
        Just ty -> do
            idFun <- mkIdentity ty
            let argVars = map Var args ++ [idFun]
            let callToTailRec = mkCoreApps (Var cpsCoreBndr) argVars
            let letExpression = mkLetRec [(cpsCoreBndr, cpsExpr)] callToTailRec
            return $ mkCoreLams args letExpression

makeContinuationType :: CoreBndr -> Type
makeContinuationType coreBndr = let
    kind = varType coreBndr
    (_, returnType) = splitFunTys kind
    in mkFunctionType Many returnType returnType

makeCPSFunTy :: CoreBndr -> Type
makeCPSFunTy coreBndr = let
    kind = varType coreBndr
    (scaledArgs, res) = splitFunTys kind
    continuationType = mkFunctionType Many res res -- Make type R -> R
    continuationResType = mkFunctionType Many continuationType res -- Make type (R -> R) -> R
    -- Make type a -> ... -> (R -> R) -> R
    funcType = foldr
        (\scaledArg funArgsType ->
            let multiplicity = scaledMult scaledArg
                argType = scaledThing scaledArg
                newArgsType = mkFunctionType multiplicity argType funArgsType
            in newArgsType)
        continuationResType
        scaledArgs
   in funcType

makeLocalCPSFun :: DynFlags -> CoreBndr -> CoreM CoreBndr
makeLocalCPSFun dflags coreBndr = let
    coreBndrName = getCoreBndrName dflags coreBndr
    localCoreBndrName = coreBndrName ++ "Aux"
    localFunTy = makeCPSFunTy coreBndr
    in makeVar localCoreBndrName localFunTy

getReturnType :: CoreBndr -> Maybe Type
getReturnType coreBndr =
  fmap (\(_, _, returnType) -> returnType) $ splitFunTy_maybe $ varType coreBndr

prependArg :: CoreExpr -> Var -> Maybe CoreExpr
prependArg expr var = aux expr where
    aux expr = case expr of
        (Lam coreBndr nextParam@(Lam _ _)) -> aux nextParam
        (Lam coreBndr expr) -> Just $ Lam coreBndr (Lam var expr)
        _ -> Nothing

makeVar :: String -> Type -> CoreM Var
makeVar name typ = do
    unique <- getUniqueM
    let varName = mkSystemVarName unique (mkFastString name)
    let var = mkLocalVar VanillaId varName Many typ vanillaIdInfo
    return var

annotationsOn :: (Data a) => ModGuts -> CoreBndr -> CoreM [a]
annotationsOn guts bndr = do
    (_, anns) <- getAnnotations deserializeWithData guts
    return $ lookupWithDefaultUFM anns [] (varName bndr)

getCoreBndrName :: DynFlags -> CoreBndr -> String
getCoreBndrName dflags coreBndr = showSDoc dflags (ppr coreBndr)

getCoreBndrNames :: DynFlags -> CoreBind -> [String]
getCoreBndrNames dflags (NonRec coreBndr _) = [getCoreBndrName dflags coreBndr]
getCoreBndrNames dflags (Rec lst) =
    map (\(coreBndr, _) -> getCoreBndrName dflags coreBndr) lst

(==>) :: Bool -> Bool -> Bool
(==>) a b = not a || b

infixr 1 ==>

getLocalBndrNames :: DynFlags -> (CoreBndr, Expr CoreBndr) -> [String]
getLocalBndrNames dflags (coreBndr, expr) = getCoreBndrName dflags coreBndr : getLocalBndrNames' expr where
    getLocalBndrNames' (Var id) = []
    getLocalBndrNames' (Lit lit) = []
    getLocalBndrNames' (App expr0 expr1) = getLocalBndrNames' expr0 ++ getLocalBndrNames' expr1
    getLocalBndrNames' (Lam coreBndr expr) = []
    getLocalBndrNames' (Let (NonRec bndr expr0) expr1) =
        getCoreBndrName dflags bndr : getLocalBndrNames' expr1
    getLocalBndrNames' (Let (Rec lst) expr) =
        getLocalBndrNames' expr ++ map (\(localBndrName, _) -> getCoreBndrName dflags localBndrName) lst
    getLocalBndrNames' (Case expr coreBndr _ alternatives) =
        getLocalBndrNames' expr ++ (alternatives >>= (\(Alt altCon coreBndrs rhs) -> getLocalBndrNames' rhs))
    getLocalBndrNames' (Cast expr _) = getLocalBndrNames' expr
    getLocalBndrNames' (Tick _ expr) = getLocalBndrNames' expr
    getLocalBndrNames' (Type typ) = []
    getLocalBndrNames' (Coercion coercion) = []

isTailRecursive :: DynFlags -> CoreBind -> Bool
isTailRecursive dflags expr = case expr of
    (NonRec coreBndr expr) -> isTailRecursive' [getCoreBndrName dflags coreBndr] expr
    (Rec lst) ->
        let coreBndrNames = getCoreBndrNames dflags (Rec lst)
        in all (\(coreBndr, expr) -> isTailRecursive' coreBndrNames expr) lst
    where
        isTailRecursive' coreBndrNames expr = case expr of
            (Var id) -> True
            (Lit lit) -> True
            (App expr0 expr1) ->
                isTailRecursive' coreBndrNames expr0
                && not (containsCallToAny dflags expr1 coreBndrNames)
                && isTailRecursive' coreBndrNames expr1 -- Test correctness
            (Lam coreBndr expr) -> isTailRecursive' coreBndrNames expr
            (Let (NonRec bndr expr0) expr1) ->
                let localBndrName = getCoreBndrName dflags bndr
                    localIsTR = isTailRecursive' (localBndrName : coreBndrNames) expr0
                in localIsTR && isTailRecursive' coreBndrNames expr1
            (Let (Rec lst) expr) -> let
                localBndrNames = getCoreBndrNames dflags (Rec lst)
                referenceableBndrNames = coreBndrNames ++ localBndrNames
                localsAreTR =all
                    (\bndr@(localBndrName, localBndrExpr) ->
                        isTailRecursive' referenceableBndrNames localBndrExpr)
                    lst
                in localsAreTR && isTailRecursive' referenceableBndrNames expr
            (Case expr coreBndr _ alternatives) ->
                isTailRecursive' coreBndrNames expr 
                && all (\(Alt altCon coreBndrs rhs) -> isTailRecursive' coreBndrNames rhs) alternatives
            (Cast expr _) -> isTailRecursive' coreBndrNames expr
            (Tick _ expr) -> isTailRecursive' coreBndrNames expr
            (Type typ) -> True
            (Coercion coercion) -> True

containsCallToAny :: DynFlags -> Expr CoreBndr -> [String] -> Bool
containsCallToAny dflags expr = any (containsCallTo dflags expr)

containsCallTo :: DynFlags -> Expr CoreBndr -> String -> Bool
containsCallTo dflags (Var id) coreBndrName = coreBndrName == showSDoc dflags (ppr id)
containsCallTo dflags (Lit lit) coreBndrName = False
containsCallTo dflags (App expr0 expr1) coreBndrName =
     containsCallTo dflags expr0 coreBndrName || containsCallTo dflags expr1 coreBndrName
containsCallTo dflags (Lam coreBndr expr) coreBndrName = containsCallTo dflags expr coreBndrName
containsCallTo dflags (Let (NonRec bndr expr0) expr1) coreBndrName = containsCallTo dflags expr1 coreBndrName -- expr0 is unused. Do something about it? Maybe?
containsCallTo dflags (Let (Rec lst) expr) coreBndrName = containsCallTo dflags expr coreBndrName -- lst is unused. Do something about it? Maybe?
containsCallTo dflags (Case expr coreBndr _ alternatives) coreBndrName =
     any (\(Alt altCon coreBndrs rhs) -> containsCallTo dflags rhs coreBndrName) alternatives
containsCallTo dflags (Cast expr _) coreBndrName = containsCallTo dflags expr coreBndrName
containsCallTo dflags (Tick _ expr) coreBndrName = containsCallTo dflags expr coreBndrName
containsCallTo dflags (Type typ) coreBndrName = False
containsCallTo dflags (Coercion coercion) coreBndrName = False

isCallToAny :: DynFlags -> CoreExpr -> [String] -> Bool
isCallToAny dflags expr = any (isCallTo dflags expr)

isCallTo :: DynFlags -> Expr CoreBndr -> String -> Bool
isCallTo dflags (Var id) coreBndrName = coreBndrName == showSDoc dflags (ppr id)
isCallTo dflags (App expr0 expr1) coreBndrName = isCallTo dflags expr0 coreBndrName
isCallTo dflags _ coreBndrName = False

printAbsyns :: DynFlags -> PrintOptions -> [(CoreBndr, Expr CoreBndr)] -> CoreM ()
printAbsyns dflags printOptions [] = return ()
printAbsyns dflags printOptions (binding : rest) = do
    printBinding dflags printOptions binding
    printAbsyns dflags printOptions rest

printBinding :: DynFlags -> PrintOptions -> (CoreBndr, Expr CoreBndr) -> CoreM ()
printBinding dflags printOptions (coreBndr, expr) = do
    putMsgS $ makeIndentation printOptions ++ "Binding: " ++ showSDoc dflags (ppr coreBndr)
    printAbsyn dflags (incInden printOptions) expr

printLine :: (Outputable a) => DynFlags -> PrintOptions -> String -> a -> CoreM ()
printLine dflags printOptions str a =
  putMsgS $ makeIndentation printOptions ++ str ++ showSDoc dflags (ppr a)

printAbsyn :: DynFlags -> PrintOptions -> Expr CoreBndr -> CoreM ()
printAbsyn dflags printOptions (Var id) =
    printLine dflags printOptions "Var " id
printAbsyn dflags printOptions (Lit lit) =
    printLine dflags printOptions "Lit " lit
printAbsyn dflags printOptions (App expr0 expr1) = do
    putMsgS $ makeIndentation printOptions ++ "App"
    printAbsyn dflags (incInden printOptions) expr0
    printAbsyn dflags (incInden printOptions) expr1
printAbsyn dflags printOptions (Lam coreBndr expr) = do
    printLine dflags printOptions "Lam " coreBndr
    printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Let (NonRec bndr expr0) expr1) = do
    printLine dflags printOptions "Let " bndr
    printAbsyn dflags (incInden printOptions) expr1
printAbsyn dflags printOptions (Let (Rec lst) expr1) = do
    putMsgS $ makeIndentation printOptions ++ "Let rec"
    printAbsyns dflags (incInden printOptions) lst
    printAbsyn dflags (incInden printOptions) expr1
printAbsyn dflags printOptions (Case expr coreBndr _ alternatives) = do
    printLine dflags printOptions "Case " coreBndr
    let printAlternatives printOptions [] = return ()
        printAlternatives printOptions ((Alt altCon coreBndrs rhs) : alts) = do
            printLine dflags printOptions "Pattern " altCon
            foldl (\acc e -> printLine dflags printOptions "Bndr " e) (pure ()) coreBndrs
            printAbsyn dflags (incInden printOptions) rhs
            printAlternatives printOptions alts
    printAlternatives (incInden printOptions) alternatives
    printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Cast expr _) = do
    putMsgS $ makeIndentation printOptions ++ "Cast"
    printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Tick _ expr) = do
    putMsgS $ makeIndentation printOptions ++ "Tick"
    printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Type typ) =
    printLine dflags printOptions "Type " typ
printAbsyn dflags printOptions (Coercion coercion) =
    printLine dflags printOptions "Coercion " coercion

printRecursive :: (Outputable b) => DynFlags -> [(b, Expr b)] -> CoreM ()
printRecursive _ [] = return ()
printRecursive dflags ((b, expr) : rest) = do
    putMsgS $ "Binding name: " ++ showSDoc dflags (ppr b)
    maybeName <- getBindingName dflags expr
    Data.Foldable.forM_ maybeName putMsgS

getBindingName :: (Outputable b) => DynFlags -> Expr b -> CoreM (Maybe String)
getBindingName dflags (Var id) = return $ Just $ "Variable: " ++ showSDoc dflags (ppr id)
getBindingName _ (Lit _) = return Nothing
getBindingName dflags (App expr0 expr1) = do
    maybeName0 <- getBindingName dflags expr0
    let name0 = fromMaybe "" maybeName0
    maybeName1 <- getBindingName dflags expr1
    let name1 = fromMaybe "" maybeName1
    return $ Just $ name0 ++ " " ++ name1
getBindingName dflags (Lam _ expr) = getBindingName dflags expr
getBindingName dflags (Let _ expr) = getBindingName dflags expr
getBindingName dflags (Case expr _ _ _) = getBindingName dflags expr
getBindingName dflags (Cast expr _) = getBindingName dflags expr
getBindingName dflags (Tick _ expr) = getBindingName dflags expr
getBindingName dflags (Type _) = return Nothing
getBindingName dflags (Coercion _) = return Nothing

callsSameFunctionTwice :: Expr a -> CoreM Bool
callsSameFunctionTwice expr = do
    names <- collectNames expr []
    unique names
    where
        collectNames (Var id) names = return $ id : names
        collectNames (Lit _) names = return names
        collectNames (App expr0 expr1) names = do
            names0 <- collectNames expr0 names
            collectNames expr1 names0
        collectNames (Lam _ expr) names = collectNames expr names
        collectNames (Let _ expr) names = collectNames expr names
        collectNames (Case expr _ _ _) names = collectNames expr names
        collectNames (Cast expr _) names = collectNames expr names
        collectNames (Tick _ expr) names = collectNames expr names
        collectNames (Type _) names = return names
        collectNames (Coercion _) names = return names

unique :: [Id] -> CoreM Bool
unique [] = return True
unique (x : xs) = do
    restUnique <- unique xs
    isElementIn <- elementIn x xs
    let notElementIn = not isElementIn
    return $ notElementIn && restUnique

elementIn :: Id -> [Id] -> CoreM Bool
elementIn a =
    foldl
        ( \accIo e -> do
            acc <- accIo
            let same = getName a == getName e
            return $ same || acc
        )
        (return False)
