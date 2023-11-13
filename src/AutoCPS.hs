module AutoCPS (plugin) where

import Control.Monad (forM_, join, mapAndUnzipM, unless, void, when)
import Data.Data
import qualified Data.Foldable
import Data.Maybe (fromMaybe, isJust)
import Data.Typeable
import Debug.Trace
import GHC.Builtin.Types (manyDataConTy)
import GHC.Core.TyCo.Rep
import GHC.Plugins
import GHC.Types.Id.Info (vanillaIdInfo)
import GHC.Types.Unique (mkLocalUnique)
import GHC.Types.Var
import Data.Foldable (find)
import qualified Data.Map as Map

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
    bindsOnlyPass (mapM (autoCPS dflags)) guts
    where
        printOptions = PrintOptions 0 " - "
        autoCPS :: DynFlags -> CoreBind -> CoreM CoreBind --(CoreBndr, Expr CoreBndr)
        autoCPS dflags bind = do
            do_transform <- case bind of
                NonRec coreBndr _ ->
                    (\anns -> "AUTO_CPS" `elem` anns) <$> (annotationsOn guts coreBndr :: CoreM [String])
                Rec lst0 -> Data.Foldable.foldl'
                    (\acc (b,e) ->
                        acc >>= \a ->
                            (\anns -> "AUTO_CPS" `elem` anns || a) <$> (annotationsOn guts b :: CoreM [String]))
                    (return False)
                    lst0
            if do_transform then do 
                cps <- transformToCPS dflags bind []
                putMsgS "Original"
                putMsgS $ showSDoc dflags (ppr bind)
                putMsgS "Transformed to CPS"
                putMsgS $ showSDoc dflags (ppr cps)
                return cps
            else return bind
        printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags bind = do
            cps <- transformToCPS dflags bind []
            case bind of
                NonRec bndr expr -> do
                    putMsgS $ showSDoc dflags $ ppr bndr
                    putMsgS $ showSDoc dflags $ ppr expr
                Rec lst -> do
                    _ <- sequence $ map (\(bndr, expr) -> do
                        putMsgS $ showSDoc dflags $ ppr bndr
                        putMsgS $ showSDoc dflags $ ppr expr) lst
                    return ()
            {-case (bind, cps) of
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
                _ -> return ()-}
            return bind

transformToCPS :: DynFlags -> CoreBind -> [CoreBndr] -> CoreM CoreBind
transformToCPS dflags bind callableFunctions = case bind of
    NonRec coreBndr expr -> do
        let callableFunctions' = coreBndr : callableFunctions
        funcToAux <- mapFunctionsToAux dflags callableFunctions'
        (transformed, aux) <- transformToCPS' funcToAux (coreBndr, expr)
        return $ Rec [transformed, aux]
    Rec lst -> do
        let callableFunctions' = map fst lst ++ callableFunctions
        funcToAux <- mapFunctionsToAux dflags callableFunctions'
        transformedFunctions <- mapM (\function -> do
            (transformed, aux) <- transformToCPS' funcToAux function
            return [transformed, aux]) lst
        return $ Rec $ join transformedFunctions
    where
        transformToCPS' :: Map.Map CoreBndr CoreBndr -> (CoreBndr, CoreExpr) -> CoreM ((CoreBndr, CoreExpr), (CoreBndr, CoreExpr))
        transformToCPS' funcToAux (coreBndr, expr) = do
            case Map.lookup coreBndr funcToAux of
                Just auxCoreBndr -> do
                    wrapperBody <- makeWrapperFunctionBody expr auxCoreBndr
                    auxBody <- transformBodyToCPS dflags (coreBndr, expr) funcToAux
                    --auxTailRecursive <- wrapCPS dflags (coreBndr, expr) (auxCoreBndr, auxBody)
                    return ((coreBndr, wrapperBody), (auxCoreBndr, auxBody))
                Nothing ->
                    return ((coreBndr, expr), (coreBndr, expr)) --This should not happen

mapFunctionsToAux :: DynFlags -> [CoreBndr] -> CoreM (Map.Map CoreBndr CoreBndr)
mapFunctionsToAux dflags functions =
    Map.fromList <$> mapM (\func -> do
        auxFunction <- makeAuxCPSFun dflags func
        return (func, auxFunction)) functions

transformBodyToCPS :: DynFlags-> (CoreBndr, CoreExpr) -> Map.Map CoreBndr CoreBndr -> CoreM CoreExpr
transformBodyToCPS dflags (coreBndr, expr) funcToAux = do
    let coreBndrName = getCoreBndrName dflags coreBndr
    continuationType <- makeContinuationType coreBndr
    continuation <- makeVar "cont" continuationType
    putMsgS $ "Transforming body of " ++ showSDoc dflags (ppr coreBndr)
    case prependArg expr continuation of
        Nothing -> return expr -- expr is not a lambda
        Just expr' -> do
            let simplifiedExpr = simplifyCases dflags expr'
            let callableFunctions = map fst $ Map.toList funcToAux
            semiTransformedBody <- transformBodyToCPS' simplifiedExpr callableFunctions continuation
            let transformedBody = replaceRecursiveCalls dflags semiTransformedBody funcToAux
            return transformedBody
    where
        transformBodyToCPS' expr callableFunctions continuation = aux expr callableFunctions True
            where
                aux expr callableFunctions inTailPosition = case expr of
                    (Var id) ->
                        if inTailPosition then
                            return $ App (Var continuation) (Var id)
                        else
                            return $ Var id
                    (Lit lit) -> return $ Lit lit
                    (App expr0 expr1) -> do
                        (exprWithBindings, newBindings) <- replaceNonTailCalls dflags (App expr0 expr1) callableFunctions
                        let hasReplacedCalls = not (null newBindings)
                        let callableFunctionNames = map (showSDoc dflags . ppr) callableFunctions
                        let isRecursiveCall = isCallToAny dflags (App expr0 expr1) callableFunctionNames
                        if hasReplacedCalls then let
                            combiningCall = App (Var continuation) exprWithBindings
                            tailRecExpr = Data.Foldable.foldl' (\acc (coreBndr, coreExpr) -> App coreExpr $ Lam coreBndr acc) combiningCall newBindings
                            in return tailRecExpr
                        else if inTailPosition then
                            if isRecursiveCall then
                                return $ App (App expr0 expr1) (Var continuation)
                            else
                                return $ App (Var continuation) exprWithBindings --Maybe use App expr0 expr1 instead (does it even matter?)
                        else
                            return $ App expr0 expr1
                    (Lam lamCoreBndr expr) -> do
                        expr' <- aux expr callableFunctions True
                        return $ Lam lamCoreBndr expr'
                    (Let (NonRec bndr expr0) expr1) ->
                        if isFunction bndr then do
                            transformedBind <- transformToCPS dflags (NonRec bndr expr0) callableFunctions
                            expr1' <- aux expr1 (bndr : callableFunctions) inTailPosition
                            return $ Let transformedBind expr1'
                        else return $ Let (NonRec bndr expr0) expr1
                    (Let (Rec lst) expr) -> do
                        transformedBind <- transformToCPS dflags (Rec lst) callableFunctions
                        expr' <- aux expr callableFunctions inTailPosition
                        return $ Let transformedBind expr'
                    (Case expr caseCoreBndr typ alternatives) -> do
                        altAsCPS <- mapM
                            (\(Alt altCon coreBndrs rhs) -> do
                                rhs' <- aux rhs callableFunctions inTailPosition
                                return $ Alt altCon coreBndrs rhs')
                            alternatives
                        (exprWithBindings, newBindings) <- replaceNonTailCalls dflags expr callableFunctions
                        let hasReplacedCalls = not (null newBindings)
                        let callableFunctionNames = map (showSDoc dflags . ppr) callableFunctions
                        let isRecursiveCall = isCallToAny dflags expr callableFunctionNames
                        if hasReplacedCalls then let
                            exprInCase = Case exprWithBindings caseCoreBndr typ altAsCPS
                            tailRecExpr = Data.Foldable.foldl' (\acc (coreBndr, coreExpr) -> App coreExpr $ Lam coreBndr acc) exprInCase newBindings
                            in return tailRecExpr
                        else if isRecursiveCall then do
                            varUnique <- getUniqueM
                            let varName = mkSystemVarName varUnique (mkFastString "contBndr")
                            let newBindingName = mkLocalVar VanillaId varName Many typ vanillaIdInfo
                            let continuationLam = Lam newBindingName (Case (Var newBindingName) caseCoreBndr typ altAsCPS)
                            let expr' = App expr continuationLam
                            return expr'
                        else
                            return $ Case expr caseCoreBndr typ altAsCPS
                    (Cast expr coercion) -> do
                        expr' <- aux expr callableFunctions False
                        return $ Cast expr' coercion
                    (Tick tickish expr) -> do
                        expr' <- aux expr callableFunctions False -- No idea if inTailPosition should actually be False
                        return $ Tick tickish expr'
                    (Type typ) -> return $ Type typ
                    (Coercion coercion) -> return $ Coercion coercion

isFunction :: CoreBndr -> Bool
isFunction = isJust . splitPiTy_maybe . varType

simplifyCases :: DynFlags -> CoreExpr -> CoreExpr
simplifyCases dflags expr = aux expr id where
    aux :: CoreExpr -> (CoreExpr -> CoreExpr) -> CoreExpr
    aux expr wrapper = case expr of
        (Var id) -> wrapper $ Var id
        (Lit lit) -> wrapper $ Lit lit
        (App expr0 expr1) ->
            aux expr0 (\x -> aux expr1 (\y -> wrapper $ App x y))
        (Lam lamCoreBndr expr) -> let
            expr' = aux expr id
            in wrapper $ Lam lamCoreBndr expr'
        (Let (NonRec bndr expr0) expr1) -> let
            expr0' = aux expr0 id
            expr1' = aux expr1 id
            in Let (NonRec bndr expr0') expr1'
        (Let (Rec lst) expr) -> let
            lst' = map (\(coreBndr, expr) -> let
                expr' = aux expr id
                in (coreBndr, expr')) lst
            expr' = simplifyCases dflags expr
            in Let (Rec lst') expr'
        (Case expr caseCoreBndr typ alternatives) -> let
            altAsCPS = map
                (\(Alt altCon coreBndrs rhs) -> case rhs of
                    Case {} -> let
                        rhs' = aux rhs wrapper
                        in  Alt altCon coreBndrs rhs'
                    _ -> let
                        rhs' = wrapper rhs
                        rhs'' = aux rhs' id
                        in Alt altCon coreBndrs rhs'')
                alternatives
            in aux expr (\x -> Case x caseCoreBndr typ altAsCPS)
        (Cast expr coercion) -> let
            expr' = aux expr (\x -> wrapper $ Cast x coercion)
            in Cast expr' coercion
        (Tick tickish expr) -> let
            expr' = aux expr (wrapper . Tick tickish)
            in Tick tickish expr'
        (Type typ) -> wrapper $ Type typ
        (Coercion coercion) -> wrapper $ Coercion coercion

indexed :: [a] -> [(Int, a)]
indexed = zip (iterate (+1) 0)

setAt :: Int -> a -> [a] -> [a]
setAt index element lst = aux index lst where
    aux index [] = lst
    aux index (x : xs)
        | index == 0 = element : xs
        | index < 0 = lst
        | index > 0 = x : aux (index - 1) xs

replaceRecursiveCalls :: DynFlags -> CoreExpr -> Map.Map CoreBndr CoreBndr -> CoreExpr
replaceRecursiveCalls dflags expr funcToAux = aux expr where
    aux expr = case expr of
        (Var id) -> case Map.lookup id funcToAux of
            Just aux -> Var aux
            Nothing -> Var id
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

replaceNonTailCalls :: DynFlags -> CoreExpr -> [CoreBndr] -> CoreM (CoreExpr, [(CoreBndr, CoreExpr)])
replaceNonTailCalls dflags expr coreBndrs = aux expr where
    aux :: CoreExpr -> CoreM (CoreExpr, [(CoreBndr, CoreExpr)])
    aux expr = case expr of
        (Var id) -> return (Var id, [])
        (Lit lit) -> return (Lit lit, [])
        (App expr0 expr1) -> do
            (expr0', newBindings0) <- aux expr0
            (expr1', newBindings1) <- aux expr1
            let maybeCall = isCallToAnyMaybe dflags expr1' coreBndrs
            case maybeCall of
                Just calledCoreBndr -> do
                    let returnType = getReturnType calledCoreBndr
                    let kind = typeKind returnType
                    tyVarUnique <- getUniqueM
                    let typeVariable = mkTyVar (mkSystemVarName tyVarUnique (mkFastString "ty")) kind
                    let tyVarTy = mkTyVarTy typeVariable
                    varUnique <- getUniqueM
                    let varName = mkSystemVarName varUnique (mkFastString "contBndr")
                    let newBindingName = mkLocalVar VanillaId varName Many tyVarTy vanillaIdInfo
                    return (App expr0' (Var newBindingName), (newBindingName, expr1') : newBindings0 ++ newBindings1)
                Nothing ->
                    return (App expr0' expr1', newBindings0 ++ newBindings1)
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
            {-(altAsCPS, newBindings0) <- mapAndUnzipM
                (\(Alt altCon coreBndrs rhs) -> do
                    (rhs', bindings) <- aux rhs
                    return (Alt altCon coreBndrs rhs', bindings))
                alternatives-}
            (expr', newBindings1) <- aux expr
            let altAsCPS = alternatives
            return (Case expr' caseCoreBndr typ altAsCPS, {-join newBindings0 ++ -}newBindings1)
        (Cast expr coercion) -> do
            (expr', newBindings) <- aux expr
            return (Cast expr' coercion, newBindings)
        (Tick tickish expr) -> do
            (expr', newBindings) <- aux expr
            return (Tick tickish expr', newBindings)
        (Type typ) -> return (Type typ, [])
        (Coercion coercion) -> return (Coercion coercion, [])

makeWrapperFunctionBody :: CoreExpr -> CoreBndr -> CoreM CoreExpr
makeWrapperFunctionBody originalCoreExpr auxCoreBndr = do
    let (tyBinders, valBinders, _) = collectTyAndValBinders originalCoreExpr
    idFun <- mkIdentityFromReturnType auxCoreBndr
    let args = map (Type . mkTyVarTy) tyBinders ++ map Var valBinders ++ [idFun]
    --let callToTailRec = mkCoreApps (Var auxCoreBndr) argVars --For some reason this crashes while the line below works
    let callToTailRec = Data.Foldable.foldl' App (Var auxCoreBndr) args
    return $ mkCoreLams (tyBinders ++ valBinders) callToTailRec

mkIdentityFromReturnType :: CoreBndr -> CoreM CoreExpr
mkIdentityFromReturnType coreBndr = do
    paramUnique <- getUniqueM
    let varName = mkSystemVarName paramUnique (mkFastString "identityParam")
    tyVarUnique <- getUniqueM
    let returnType = getReturnType coreBndr
    let kind = typeKind returnType
    let typeVariable = mkTyVar (mkSystemVarName tyVarUnique (mkFastString "ty")) kind
    let tyVarTy = mkTyVarTy typeVariable
    let var = mkLocalVar VanillaId varName Many tyVarTy vanillaIdInfo
    return $ mkCoreLams [var] (Var var)

wrapCPS :: (CoreBndr, CoreExpr) -> (CoreBndr, CoreExpr) -> CoreM CoreExpr
wrapCPS (originalCoreBndr, originalExpr) (cpsCoreBndr, cpsExpr) = do
    let (args, _) = collectBinders originalExpr
    let returnType = getReturnType originalCoreBndr
    idFun <- mkIdentityFromReturnType originalCoreBndr
    let argVars = map Var args ++ [idFun]
    let callToTailRec = mkCoreApps (Var cpsCoreBndr) argVars
    let letExpression = mkLetRec [(cpsCoreBndr, cpsExpr)] callToTailRec
    return $ mkCoreLams args letExpression

makeContinuationType :: CoreBndr -> CoreM Type
makeContinuationType coreBndr = do
    let kind = varType coreBndr
    let (_, returnType) = splitFunTys kind
    let kind = typeKind returnType
    paramTyVarUnique <- getUniqueM
    returnTyVarUnique <- getUniqueM
    let paramTypeVariable = mkTyVar (mkSystemVarName paramTyVarUnique (mkFastString "paramTy")) kind
    let returnTypeVariable = mkTyVar (mkSystemVarName returnTyVarUnique (mkFastString "returnTy")) kind
    let paramTyVarTy = mkTyVarTy paramTypeVariable
    let returnTyVarTy = mkTyVarTy returnTypeVariable
    return $ mkFunctionType Many paramTyVarTy returnTyVarTy

makeCPSFunTy :: CoreBndr -> CoreM Type
makeCPSFunTy coreBndr = do
    let kind = varType coreBndr
    let (tyCoBinders, res) = splitPiTys kind
    let continuationType = mkFunctionType Many res res -- Make type R -> R
    let continuationResType = mkFunctionType Many continuationType res -- Make type (R -> R) -> R
    let funcType = mkPiTys tyCoBinders continuationResType
    return funcType

makeAuxCPSFun :: DynFlags -> CoreBndr -> CoreM CoreBndr
makeAuxCPSFun dflags coreBndr = do
    let coreBndrName = getCoreBndrName dflags coreBndr
    let localCoreBndrName = coreBndrName ++ "Aux"
    localFunTy <- makeCPSFunTy coreBndr
    makeVar localCoreBndrName localFunTy

getReturnType :: CoreBndr -> Type
getReturnType coreBndr = let
    kind = varType coreBndr
    (_, returnType) = splitFunTys kind
    in returnType

prependArg :: CoreExpr -> Var -> Maybe CoreExpr
prependArg expr var = aux expr where
    aux expr = case expr of
        (Lam coreBndr nextParam@(Lam _ _)) -> aux nextParam >>= (Just . Lam coreBndr)
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

isCallToAnyMaybe :: DynFlags -> CoreExpr -> [CoreBndr] -> Maybe CoreBndr
isCallToAnyMaybe dflags expr coreBndrs =
    join $
    find isJust $
    map (\coreBndr ->
        if isCallTo dflags expr (getCoreBndrName dflags coreBndr)
            then Just coreBndr
            else Nothing)
        coreBndrs

isCallToAny :: DynFlags -> CoreExpr -> [String] -> Bool
isCallToAny dflags expr = any (isCallTo dflags expr)

isCallTo :: DynFlags -> CoreExpr -> String -> Bool
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
            Data.Foldable.foldl' (\acc e -> printLine dflags printOptions "Bndr " e) (pure ()) coreBndrs
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
    Data.Foldable.foldl'
        ( \accIo e -> do
            acc <- accIo
            let same = getName a == getName e
            return $ same || acc
        )
        (return False)
