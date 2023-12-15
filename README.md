# AutoCPS
A plugin for Haskell that automatically transforms any non-tail recursive function to a tail-recursive function using continuation-passing style.
A function is transformed to CPS by annotating it with {-# ANN <functionName> "AUTO_CPS" #-}.  
Works with GHC 9.4.7.  

Run tests by using "cabal run".
