module Main where

import CPSTests (correctness_check, performance_check, single, find_breaking_point, fibonnaci, reverse_lst_auto)
import Test.QuickCheck

main :: IO ()
main = correctness_check

{-
Factorial
Fum
Tower of Hanoi
Fibonacci
Palimdrome
String reversal
Ackermann function
Sum of elements in list
-}

{-# ANN mutuallyTailRec0 "AUTO_CPS" #-}
mutuallyTailRec0 :: Int -> Int
mutuallyTailRec0 n = mutuallyTailRec1 (n - 1)

mutuallyTailRec1 :: Int -> Int
mutuallyTailRec1 n = mutuallyTailRec0 (n - 1)

{-# ANN matchOnLet "AUTO_CPS" #-}
matchOnLet :: Int -> Int
matchOnLet n = case let a = n * n in a * a of
    0 -> 0
    _ -> 1 + matchOnLet (n - 1)

matchOnLet1 :: Int -> Int
matchOnLet1 n = case let a = n * n in a * a of
    0 -> 0
    _ -> 1 + matchOnLet1 (n - 1)

{-# ANN matchOnRecCase "AUTO_CPS" #-}
matchOnRecCase :: Int -> Int
matchOnRecCase n = case case n of
    0 -> 0
    _ -> 1 + matchOnRecCase (n - 1) of
    0 -> 0
    _ -> 1 + matchOnRecCase (n - 1)

matchOnRecCase1 :: Int -> Int
matchOnRecCase1 n = case case n of
    0 -> 0
    _ -> 1 + matchOnRecCase1 (n - 1) of
    0 -> 0
    _ -> 1 + matchOnRecCase1 (n - 1)

{-# ANN matchOnCase "AUTO_CPS" #-}
matchOnCase :: Int -> Int
matchOnCase n = case case n of
    0 -> 0
    _ -> 1 of
    0 -> 0
    _ -> 1 + matchOnCase (n - 1)

matchOnCaseC :: Int -> Int
matchOnCaseC n = aux n id where
    aux n c = case case n of
        0 -> 0
        _ -> 1 of
        0 -> c 0
        _ -> aux (n - 1) (\x -> c (x + 1))

{-# ANN aaa "AUTO_CPS" #-}
aaa :: Int -> Int
aaa n = case n of
    0 -> aaa (n - 1)
    _ -> 9

{-# ANN recCallInCase2 "AUTO_CPS" #-}
recCallInCase2 :: Int -> Int
recCallInCase2 n = case recCallInCase2 n + 1 of
    0 -> 1
    _ -> n

recCallInCase2C :: Int -> Int
recCallInCase2C n = recCallInCaseC2Aux n id

{-# ANN recCallInCaseC2Aux "AUTO_CPS" #-}
recCallInCaseC2Aux :: Int -> (Int -> Int) -> Int
recCallInCaseC2Aux n c =
    recCallInCaseC2Aux n (\x -> case x + 1 of
        0 -> c 1
        _ -> c n)

{-# ANN recCallInCase "AUTO_CPS" #-}
recCallInCase :: Int -> Int
recCallInCase n = case recCallInCase n of
    0 -> 1
    _ -> n

recCallInCaseC :: Int -> Int
recCallInCaseC n = recCallInCaseCAux n id

recCallInCaseCAux :: Int -> (Int -> Int) -> Int
recCallInCaseCAux n c =
    recCallInCaseCAux n (\x -> case x of
        0 -> c 1
        _ -> c n)

{-# ANN expressionInCase "AUTO_CPS" #-}
expressionInCase :: Int -> Int
expressionInCase n = case n < 4 of
    True -> expressionInCase 0
    False -> expressionInCase 1

{-# ANN innerCallsOuter "AUTO_CPS" #-}
innerCallsOuter :: Int -> Int
innerCallsOuter n = inner n where
    inner n = outerCalledByInner n

outerCalledByInner :: Int -> Int
outerCalledByInner n = innerCallsOuter n

innerCallsOuterC :: Int -> Int
innerCallsOuterC n = inner n where
    inner n = outerCalledByInnerC n

outerCalledByInnerC :: Int -> Int
outerCalledByInnerC n = innerCallsOuterC n

{-# ANN nonRecWithLocalRec "AUTO_CPS" #-}
nonRecWithLocalRec :: Int -> Int
nonRecWithLocalRec n = aux n where
    aux 0 = 0
    aux n = 1 + aux (n - 1)

{-# ANN mutuallyRecursive0 "AUTO_CPS" #-}
mutuallyRecursive0 :: Int -> Int
mutuallyRecursive0 0 = 0
mutuallyRecursive0 n = mutuallyRecursive1 (n - 1) + 1

mutuallyRecursive1 :: Int -> Int
mutuallyRecursive1 0 = 1
mutuallyRecursive1 n = mutuallyRecursive0 (n - 1) + 1

{-# ANN mutuallyRecursive0C "AUTO_CPS" #-}
mutuallyRecursive0C :: Int -> Int
mutuallyRecursive0C n = mutuallyRecursive0CAux n id

mutuallyRecursive0CAux n c = case n of
    0 -> c 0
    _ -> mutuallyRecursive1CAux (n - 1) (\x -> c (x + 1))

mutuallyRecursive1C :: Int -> Int
mutuallyRecursive1C n = mutuallyRecursive0CAux n id

mutuallyRecursive1CAux n c = case n of
    0 -> c 1
    _ -> mutuallyRecursive0CAux (n - 1) (\x -> c (x + 1))

{-# ANN iHaveNoIdeaWhatToCallThis "AUTO_CPS" #-}
iHaveNoIdeaWhatToCallThis :: Int -> String
iHaveNoIdeaWhatToCallThis 0 = "0"
iHaveNoIdeaWhatToCallThis n = show (ohLookAnotherFunction (show (n - 1)))

ohLookAnotherFunction :: String -> Int
ohLookAnotherFunction str = length (iHaveNoIdeaWhatToCallThis 0)

{-# ANN doubleNestedLetNonRecBinding "AUTO_CPS" #-}
doubleNestedLetNonRecBinding :: Int -> Int
doubleNestedLetNonRecBinding n = case n of
    0 -> 0
    _ -> let
        a = let
            b = n * n
            in doubleNestedLetNonRecBinding (b + b)
        in a + a

{-# ANN doubleNestedLetRecBinding "AUTO_CPS" #-}
doubleNestedLetRecBinding :: Int -> Int
doubleNestedLetRecBinding n = case n of
    0 -> 0
    _ -> let
        f a = case a of
            0 -> 0
            _ -> let
                g b = case b of
                    0 -> 0
                    _ -> 1 + g (b - 1)
                in f (g a)
        in doubleNestedLetRecBinding (n - 1) + f (n - 1)

{-# ANN nonRecLetBindingTest "AUTO_CPS" #-}
nonRecLetBindingTest :: Int -> Int -> Int
nonRecLetBindingTest n m = case n of
    0 -> m
    _ -> let
        a = n - 1
        in nonRecLetBindingTest a a

{-# ANN appPlusToLetBinding "AUTO_CPS" #-}
appPlusToLetBinding :: Int -> Int
appPlusToLetBinding n = case n of
    0 -> 0
    _ -> 1 + let
        a = appPlusToLetBinding (n - 1)
        in a * a

{-# ANN fourthLetBindingTest "AUTO_CPS" #-}
fourthLetBindingTest :: Int -> Int
fourthLetBindingTest n = case n of
    0 -> 0
    _ -> let
        b = a * 8 + a
        a = n * n
        c = let
            f n = case n of
                0 -> 0
                _ -> n + f (n - 1)
            in f n
        in a + b + b * fourthLetBindingTest (n - 1) + c * c

fourthLetBindingTestC :: Int -> (Int -> Int) -> Int
fourthLetBindingTestC n c = case n of
    0 -> c 0
    _ -> let
        b = a * 8 + a
        a = n * n
        f n k = case n of
            0 -> k 0
            _ -> f (n - 1) (\x -> k (x + n))
        in f a (\x -> fourthLetBindingTestC (n - 1) (\y -> c (a + b + b * y + x * x)))

{-# ANN thirdLetBindingTest "AUTO_CPS" #-}
thirdLetBindingTest :: Int -> Int
thirdLetBindingTest n = case n of
    0 -> 0
    _ -> let
        b = a * 8 + a
        a = n * n
        in a + b + b * thirdLetBindingTest (n - 1)

{-# ANN anotherLetBindingTest "AUTO_CPS" #-}
anotherLetBindingTest :: Int -> Int -> Int
anotherLetBindingTest n m = case n of
    0 -> m
    _ -> let
        a = anotherLetBindingTest (n - 1) (m - 1)
        f n = case n of
            0 -> a
            _ -> n + f (n - 1)
        b = f n
        in a + b

{-# ANN letBindingTest "AUTO_CPS" #-}
letBindingTest :: Int -> Int -> Int
letBindingTest n m = case n of
    0 -> m
    _ -> let
        a = letBindingTest (n - 1) (m - 1)
        in a + a

letBindingTestC :: Int -> Int -> Int
letBindingTestC n m = letBindingTestCAux n m id

letBindingTestCAux :: Int -> Int -> (Int -> Int) -> Int
letBindingTestCAux n m c = case n of
    0 -> c m
    _ -> letBindingTestCAux (n - 1) (m - 1) (\a -> a + a)

{-# ANN generic "AUTO_CPS" #-}
generic :: a -> b
generic a = generic a

{-caseInApp :: Int -> Int
caseInApp 0 = 0
caseInApp n = 1 + case n of
    0 -> 0
    n -> caseInApp (n - 1)-}

{-caseInAppC :: Int -> Int
caseInAppC n = aux n id where
    aux 0 c = c 0
    aux n c = case n of
        0 -> c 1
        n -> aux (n - 1) (\x -> c (x + 1))-}

{-# ANN caseInApp2 "AUTO_CPS" #-}
caseInApp2 :: Int -> Int
caseInApp2 n = 1 + case n of
    0 -> 0
    n -> caseInApp2 (n - 1)

caseInApp2C :: Int -> Int
caseInApp2C n = aux n id where
    aux n c = case n of
        0 -> c 1
        n -> aux (n - 1) (\x -> c (1 + x))

{-# ANN caseInAppInCaseInApp "AUTO_CPS" #-}
caseInAppInCaseInApp :: Int -> Int -> Int
caseInAppInCaseInApp n m = 1 + case n of
    0 -> 0
    n -> 1 + case m of
        0 -> 0
        m -> caseInAppInCaseInApp (n - 1) (m - 1)

{-# ANN caseInAppInCaseInApp2 "AUTO_CPS" #-}
caseInAppInCaseInApp2 :: Int -> Int -> Int
caseInAppInCaseInApp2 n m = case n of
    0 -> 1
    n -> case m of
        0 -> 2
        m -> 2 + caseInAppInCaseInApp2 (n - 1) (m - 1)

--manyArgs :: Int -> Float -> Bool -> String -> Bool
--manyArgs n f b s = False

{-# ANN foo "AUTO_CPS" #-}
foo :: Int -> Int -> Int
foo a b = a + b + foo (a - 1) (b - 1)

{-# ANN bar "AUTO_CPS" #-}
bar :: Int -> Int
bar 0 = 0
bar n = n + bar (n - 1)

{-# ANN fib "AUTO_CPS" #-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

fibC :: Int -> Int
fibC n = aux n id where
    aux 0 c = c 0
    aux 1 c = c 1
    aux n c = aux (n - 1) (\x -> aux (n - 2) (\y -> c (x + y)))
