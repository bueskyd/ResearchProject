module Main where

import CPSTests (test)

main :: IO ()
main = do
    print $ meme 7
    --mapM_ (print . fib) $ take 10 $ iterate (1+) 0
    --print $ bar 10
    --print $ caseInApp2C 7
    {-print $ caseInAppInCaseInApp 7 4
    print $ caseInAppInCaseInApp 13 3
    print $ caseInAppInCaseInApp 6 12
    print $ caseInAppInCaseInApp 9 43-}
    --mapM_ (\n -> print $ mutuallyRecursive0 n == mutuallyRecursive0C n) $ take 10 $ iterate (+1) 0
    --mapM_ (putStrLn . iHaveNoIdeaWhatToCallThis) $ take 10 $ iterate (+1) 0
    --mapM_ (print . nonRecWithLocalRec) $ take 10 $ iterate (+1) 0
    --test
    --mapM_ print (reverse_lst [1,2,3,4,5,6,7,8,9,0])

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

--{-# ANN aaa "AUTO_CPS" #-}
aaa :: Int -> Int
aaa n = case n of
    0 -> aaa (n - 1)
    _ -> 9

--{-# ANN recCallInCase2 "AUTO_CPS" #-}
recCallInCase2 :: Int -> Int
recCallInCase2 n = case recCallInCase2 n + 1 of
    0 -> 1
    _ -> n

recCallInCase2C :: Int -> Int
recCallInCase2C n = recCallInCaseC2Aux n id

--{-# ANN recCallInCaseC2Aux "AUTO_CPS" #-}
recCallInCaseC2Aux :: Int -> (Int -> Int) -> Int
recCallInCaseC2Aux n c =
    recCallInCaseC2Aux n (\x -> case x + 1 of
        0 -> c 1
        _ -> c n)

--{-# ANN recCallInCase "AUTO_CPS" #-}
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

--{-# ANN expressionInCase "AUTO_CPS" #-}
expressionInCase :: Int -> Int
expressionInCase n = case n < 4 of
    True -> expressionInCase 0
    False -> expressionInCase 1

--{-# ANN innerCallsOuter "AUTO_CPS" #-}
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

--{-# ANN nonRecWithLocalRec "AUTO_CPS" #-}
nonRecWithLocalRec :: Int -> Int
nonRecWithLocalRec n = aux n where
    aux 0 = 0
    aux n = 1 + aux (n - 1)

--{-# ANN mutuallyRecursive0 "AUTO_CPS" #-}
mutuallyRecursive0 :: Int -> Int
mutuallyRecursive0 0 = 0
mutuallyRecursive0 n = mutuallyRecursive1 (n - 1) + 1

mutuallyRecursive1 :: Int -> Int
mutuallyRecursive1 0 = 1
mutuallyRecursive1 n = mutuallyRecursive0 (n - 1) + 1

--{-# ANN mutuallyRecursive0C "AUTO_CPS" #-}
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

--{-# ANN iHaveNoIdeaWhatToCallThis "AUTO_CPS" #-}
iHaveNoIdeaWhatToCallThis :: Int -> String
iHaveNoIdeaWhatToCallThis 0 = "0"
iHaveNoIdeaWhatToCallThis n = show (ohLookAnotherFunction (show (n - 1)))

ohLookAnotherFunction :: String -> Int
ohLookAnotherFunction str = length (iHaveNoIdeaWhatToCallThis 0)

nonRecLetBindingTest :: Int -> Int -> Int
nonRecLetBindingTest n m = case n of
    0 -> m
    _ -> let
        a = n - 1
        in nonRecLetBindingTest a a

--{-# ANN letBindingTest "AUTO_CPS" #-}
letBindingTest :: Int -> Int -> Int
letBindingTest n m = case n of
    0 -> m
    _ -> let
        a = letBindingTest (n - 1) (m - 1)
        in a + a

{-letBindingTestC :: Int -> Int -> Int
letBindingTestC n m = letBindingTestCAux n m id

letBindingTestCAux :: Int -> Int -> (Int -> Int) -> Int
letBindingTestCAux n m c = case n of
    0 -> c m
    _ -> letBindingTestCAux a a ()-}

--{-# ANN generic "AUTO_CPS" #-}
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

--{-# ANN caseInApp2 "AUTO_CPS" #-}
caseInApp2 :: Int -> Int
caseInApp2 n = 1 + case n of
    0 -> 0
    n -> caseInApp2 (n - 1)

caseInApp2C :: Int -> Int
caseInApp2C n = aux n id where
    aux n c = case n of
        0 -> c 1
        n -> aux (n - 1) (\x -> c (1 + x))

--{-# ANN caseInAppInCaseInApp "AUTO_CPS" #-}
caseInAppInCaseInApp :: Int -> Int -> Int
caseInAppInCaseInApp n m = 1 + case n of
    0 -> 0
    n -> 1 + case m of
        0 -> 0
        m -> caseInAppInCaseInApp (n - 1) (m - 1)

--{-# ANN caseInAppInCaseInApp2 "AUTO_CPS" #-}
caseInAppInCaseInApp2 :: Int -> Int -> Int
caseInAppInCaseInApp2 n m = case n of
    0 -> 1
    n -> case m of
        0 -> 2
        m -> 2 + caseInAppInCaseInApp2 (n - 1) (m - 1)

--manyArgs :: Int -> Float -> Bool -> String -> Bool
--manyArgs n f b s = False

--{-# ANN foo "AUTO_CPS" #-}
foo :: Int -> Int -> Int
foo a b = a + b + foo (a - 1) (b - 1)

--{-# ANN bar "AUTO_CPS" #-}
bar :: Int -> Int
bar 0 = 0
bar n = n + bar (n - 1)

{-fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)-}

{-fibC :: Int -> Int
fibC n = aux n id where
    aux 0 c = c 0
    aux 1 c = c 1
    aux n c = aux (n - 1) (\x -> aux (n - 2) (\y -> c (x + y)))-}

--{-# ANN meme "AUTO_CPS" #-}
meme :: Int -> Int
meme n = if n <= 0 then 0 else (meme (meme (n - 1))) - 1

{-memeC :: Int -> Int
memeC n = aux n id where
    aux n c =
        if n <= 0 then
            c 0
        else
            aux (n - 1) (\x -> aux x (\y -> c (y - 1)))-}

{-barA :: Int -> Int-> Int
barA 0 acc = acc
barA n acc = barA (n - 1) (acc + n)-}

{-barT :: Int -> Int
barT n = aux n id
    where
        aux 0 c = c 0
        aux n c = aux (n - 1) (\x -> c $ n + x)-}
        
{-baz :: Int -> Int -> Float
baz 0 _ = 0.0
baz _ 0 = 0.0
baz a b = baz (a - 1) (b - 2) + 1.0-}

{-tailRec0 :: Int -> Int
tailRec0 0 = 0
tailRec0 1 = 1
tailRec0 n = tailRec1 (n - 1)

tailRec1 :: Int -> Int
tailRec1 0 = 0
tailRec1 1 = 1
tailRec1 n = tailRec0 (n - 2)

{-# ANN foo "AUTO_CPS" #-}
{-# ANN tailRec0 "AUTO_CPS" #-}
{-# ANN tailRec1 "AUTO_CPS" #-}
shouldNotBeTailRec0 :: Int -> Int
shouldNotBeTailRec0 0 = 0
shouldNotBeTailRec0 n = shouldNotBeTailRec0 (aux n)
    where
        aux 0 = 0
        aux n = aux (n - 1) - 1

shouldNotBeTailRec1 :: Int -> Int
shouldNotBeTailRec1 0 = 0
shouldNotBeTailRec1 n = shouldNotBeTailRec1 (n - 1) - 1

shouldBeTailRec0 :: Int -> Int
shouldBeTailRec0 n = shouldBeTailRec0 n where
    shouldBeTailRec0 0 = 0
    shouldBeTailRec0 n = shouldBeTailRec0 (n - 1)
    
letInLet :: Int -> Int
letInLet n = let
    x = let
        y = 8
        in y
    in x

letInIn :: Int -> Int
letInIn n = let
    x = 7
    in
        let
            y = 3
            in y

doubleLet :: Int -> Int
doubleLet n = let
    x = 7
    y = 8
    in x + y
-}