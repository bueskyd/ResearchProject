module PluginTest (plugin) where
import GHC.Plugins
import Data.Maybe (fromMaybe)

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
  where printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags bndr@(NonRec b expr) = do
          putMsgS "Printing non-recursive function"
          printAbsyns dflags [(b, expr)]
          return bndr
        printBind dflags bndr@(Rec lst) = do
          putMsgS "Printing recursive functions"
          printAbsyns dflags lst
          return bndr

printAbsyns :: DynFlags -> [(CoreBndr, Expr CoreBndr)] -> CoreM ()
printAbsyns dlfas [] = return ()
printAbsyns dflags ((coreBndr, expr) : rest) = do
  putMsgS $ "Binding: " ++ showSDoc dflags (ppr coreBndr)
  printAbsyn dflags 0 '-' expr

printLine :: Outputable a => DynFlags -> Int -> Char -> String -> a -> CoreM ()
printLine dflags indentation char str a =
  putMsgS $ replicate indentation char ++ str ++ showSDoc dflags (ppr a)

printAbsyn :: DynFlags -> Int -> Char -> Expr CoreBndr -> CoreM ()
printAbsyn dflags indentation char (Var id) =
  printLine dflags indentation char "Var " id
printAbsyn dflags indentation char (Lit lit) =
  printLine dflags indentation char "Lit " lit
printAbsyn dflags indentation char (App expr0 expr1) = do
  putMsgS $ replicate indentation char ++ "App"
  printAbsyn dflags (indentation + 1) char expr0
  printAbsyn dflags (indentation + 1) char expr1
printAbsyn dflags indentation char (Lam coreBndr expr) = do
  printLine dflags indentation char "Lam " coreBndr
  printAbsyn dflags (indentation + 1) char expr

printAbsyn dflags indentation char (Let (NonRec bndr expr0) expr1) = do
  putMsgS $ replicate indentation char ++ "Let"
  printAbsyn dflags (indentation + 1) char expr1
printAbsyn dflags indentation char (Let (Rec lst) expr1) = do --This case is not done
  putMsgS $ replicate indentation char ++ "Let"
  printAbsyn dflags (indentation + 1) char expr1

printAbsyn dflags indentation char (Case expr coreBndr _ alternatives) = do
  printLine dflags indentation char "Case " coreBndr
  let printAlternatives indentation [] = return ()
      printAlternatives indentation ((Alt altCon coreBndrs rhs) : alts) = do
        printLine dflags indentation char "Pattern " altCon
        foldl (\acc e -> printLine dflags indentation char "Bndr " e) (pure ()) coreBndrs
        printAbsyn dflags (indentation + 1) char rhs
        printAlternatives indentation alts
  printAlternatives (indentation + 1) alternatives
  printAbsyn dflags (indentation + 1) char expr

printAbsyn dflags indentation char (Cast expr _) = do
  putMsgS $ replicate indentation char ++ "Cast"
  printAbsyn dflags (indentation + 1) char expr
printAbsyn dflags indentation char (Tick _ expr) = do
  putMsgS $ replicate indentation char ++ "Tick"
  printAbsyn dflags (indentation + 1) char expr
printAbsyn dflags indentation char (Type typ) =
  printLine dflags indentation char "Type " typ
printAbsyn dflags indentation char (Coercion coercion) =
  printLine dflags indentation char "Coercion " coercion

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
