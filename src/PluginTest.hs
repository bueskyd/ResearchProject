module PluginTest (plugin) where
import GHC.Plugins

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
          putMsgS $ "Non-recursive binding named " ++ showSDoc dflags (ppr b)
          if hasVariableNamedFoo expr then putMsgS "succ" else putMsgS "Disse"
          return bndr
        printBind _ bndr = return bndr
 
hasVariableNamedFoo :: (Expr a) -> Bool
hasVariableNamedFoo (Var id) = (show $ getName id) == "putStrLn"

hasVariableNamedFoo (Lit _) = False
hasVariableNamedFoo (App expr _) = hasVariableNamedFoo expr
hasVariableNamedFoo (Lam _ expr) = hasVariableNamedFoo expr
hasVariableNamedFoo (Let _ expr) = hasVariableNamedFoo expr
hasVariableNamedFoo (Case expr _ _ _) = hasVariableNamedFoo expr
hasVariableNamedFoo (Cast expr _) = hasVariableNamedFoo expr
hasVariableNamedFoo (Tick _ expr) = hasVariableNamedFoo expr
hasVariableNamedFoo (Type _) = False
hasVariableNamedFoo (Coercion _) = False
