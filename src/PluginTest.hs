module PluginTest (plugin) where
import GHC.Plugins
import Data.Maybe (fromMaybe)

data PrintOptions = PrintOptions { indentation :: Int, indentationString :: String }

incInden :: PrintOptions -> PrintOptions
incInden printOptions = PrintOptions (indentation printOptions + 1) (indentationString printOptions)

makeIndentation :: PrintOptions -> String
makeIndentation printOptions =
  replicate (indentation printOptions) (indentationString printOptions) >>= id

plugin :: Plugin
plugin = defaultPlugin {
    installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
    return (CoreDoPluginPass "Hi mom" pass : todo)

pass :: ModGuts -> CoreM ModGuts
pass guts = do dflags <- getDynFlags
               bindsOnlyPass (mapM (printBind dflags)) guts
  where
        printOptions = PrintOptions 0 " - "
        printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags bndr@(NonRec b expr) = do
          putMsgS "Printing non-recursive function"
          --printAbsyns dflags printOptions [(b, expr)]
          putMsgS $ showSDoc dflags (ppr b)
          return bndr
        printBind dflags bndr@(Rec lst) = do
          putMsgS "Printing recursive functions"
          putMsgS $ getCoreBndrName dflags (fst $ head $ lst)
          putMsgS $ "Tail recursive: " ++ (show $ isTailRecursive dflags bndr)
          --printAbsyns dflags printOptions lst
          return bndr

getCoreBndrName :: DynFlags -> CoreBndr -> String
getCoreBndrName dflags coreBndr = showSDoc dflags (ppr coreBndr)

isTailRecursive :: DynFlags -> CoreBind -> Bool
isTailRecursive _ (NonRec _ _) = False
isTailRecursive dflags (Rec lst) =
  all (\(coreBndr, expr) ->
    let coreBndrName = getCoreBndrName dflags coreBndr
    in isTailRecursive' coreBndrName expr) lst
  where
    isTailRecursive' coreBndrName (Var id) = True
    isTailRecursive' coreBndrName (Lit lit) = True
    isTailRecursive' coreBndrName (App expr0 expr1) = isCallTo dflags expr0 coreBndrName
    isTailRecursive' coreBndrName (Lam coreBndr expr) = isTailRecursive' coreBndrName expr --Probably not correct
    isTailRecursive' coreBndrName (Let (NonRec bndr expr0) expr1) = isTailRecursive' coreBndrName expr1 --expr0 is unused. Do something about it.
    isTailRecursive' coreBndrName (Let (Rec lst) expr) = isTailRecursive' coreBndrName expr --lst is unused. Do something about it.
    isTailRecursive' coreBndrName (Case expr coreBndr _ alternatives) =
      all (\(Alt altCon coreBndrs rhs) -> isTailRecursive' coreBndrName rhs) alternatives
    isTailRecursive' coreBndrName (Cast expr _) = isTailRecursive' coreBndrName expr
    isTailRecursive' coreBndrName (Tick _ expr) = isTailRecursive' coreBndrName expr
    isTailRecursive' coreBndrName (Coercion coercion) = True

isCallTo :: DynFlags -> Expr CoreBndr -> String -> Bool
isCallTo dflags (Var id) coreBndrName = coreBndrName == showSDoc dflags (ppr id)
isCallTo dflags (App expr0 expr1) coreBndrName = isCallTo dflags expr0 coreBndrName
isCallTo dflags _ coreBndrName = False

printAbsyns :: DynFlags -> PrintOptions -> [(CoreBndr, Expr CoreBndr)] -> CoreM ()
printAbsyns dflags printOptions [] = return ()
printAbsyns dflags printOptions (binding : rest) = do
  printLine dflags printOptions "" binding
  printBinding dflags printOptions binding
  printAbsyns dflags printOptions rest

printBinding :: DynFlags -> PrintOptions -> (CoreBndr, Expr CoreBndr) -> CoreM ()
printBinding dflags printOptions (coreBndr, expr) = do
  putMsgS $ (makeIndentation printOptions) ++ "Binding: " ++ showSDoc dflags (ppr coreBndr)
  printAbsyn dflags (incInden printOptions) expr

printLine :: Outputable a => DynFlags -> PrintOptions -> String -> a -> CoreM ()
printLine dflags printOptions str a =
  putMsgS $ (makeIndentation printOptions) ++ str ++ showSDoc dflags (ppr a)

printAbsyn :: DynFlags -> PrintOptions -> Expr CoreBndr -> CoreM ()
printAbsyn dflags printOptions (Var id) =
  printLine dflags printOptions "Var " id
printAbsyn dflags printOptions (Lit lit) =
  printLine dflags printOptions "Lit " lit
printAbsyn dflags printOptions (App expr0 expr1) = do
  putMsgS $ (makeIndentation printOptions) ++ "App"
  printAbsyn dflags (incInden printOptions) expr0
  printAbsyn dflags (incInden printOptions) expr1
printAbsyn dflags printOptions (Lam coreBndr expr) = do
  printLine dflags printOptions "Lam " coreBndr
  printAbsyn dflags (incInden printOptions) expr

printAbsyn dflags printOptions (Let (NonRec bndr expr0) expr1) = do
  printLine dflags printOptions "Let " bndr
  printAbsyn dflags (incInden printOptions) expr1
printAbsyn dflags printOptions (Let (Rec lst) expr1) = do
  putMsgS $ (makeIndentation printOptions) ++ "Let"
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
  putMsgS $ (makeIndentation printOptions) ++ "Cast"
  printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Tick _ expr) = do
  putMsgS $ (makeIndentation printOptions) ++ "Tick"
  printAbsyn dflags (incInden printOptions) expr
printAbsyn dflags printOptions (Type typ) =
  printLine dflags printOptions "Type " typ
printAbsyn dflags printOptions (Coercion coercion) =
  printLine dflags printOptions "Coercion " coercion

printRecursive :: Outputable b => DynFlags -> [(b, Expr b)] -> CoreM ()
printRecursive _ [] = return ()
printRecursive dflags ((b, expr) : rest) = do
  putMsgS $ "Binding name: " ++ showSDoc dflags (ppr b)
  maybeName <- getBindingName dflags expr
  case maybeName of
    Just name -> putMsgS name
    Nothing -> return ()

getBindingName :: Outputable b => DynFlags -> Expr b -> CoreM (Maybe String)
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
elementIn a = foldl (\accIo e -> do
  acc <- accIo
  let same = getName a == getName e
  --if same then putMsgS $ occNameString $ getOccName a else return ()
  return $ same || acc) (return False)
