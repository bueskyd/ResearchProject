{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}


module CPSTests where

import GHC.List hiding (concat)
import Prelude hiding (foldl)
import System.Random

import Test.QuickCheck

small_nat :: Gen Int
small_nat = abs `fmap` (arbitrary :: Gen Int) `suchThat` (\i -> (i >= 0) &&  (i < 20))

prop_rev_lst :: [Int] -> Bool
prop_rev_lst lst = reverse_lst lst == reverse_lst_cps lst

prop_palindrome :: [Int] -> Bool
prop_palindrome lst = palindrome lst == palindrome_cps lst

prop_sum_lst :: [Int] -> Bool
prop_sum_lst lst = sum_list lst == sum_list_cps lst

prop_fibonnaci :: Int -> Bool
prop_fibonnaci i = fibonnaci i == fibonnaci_cps i

prop_factorial :: Int -> Bool
prop_factorial i = fibonnaci i == fibonnaci_cps i

do_test :: IO ()
do_test = do
    putStrLn "Testing\n"
    quickCheck $ forAll small_nat $ prop_factorial
    quickCheck $ forAll small_nat $ prop_fibonnaci
    quickCheck prop_palindrome
    quickCheck prop_sum_lst
    quickCheck prop_rev_lst
    
-- Try to use quick-check
-- Try framework 'critriion' for performance testing
{-test :: IO ()
test = do
    g <- getStdGen
    positive_ints <- sequence $ replicate 10 $ randomRIO (1,10::Int)
    positive_list <- mapM (\i -> sequence $ replicate i $ randomRIO (1,10::Int)) positive_ints
    -- Int -> Int
    ffuzz_print (ffuzz_run 
        [
            ("Factorial", factorial, factorial_cps),
            ("SumTo", sum_to, sum_to_cps),
            ("Fibonnaci", fibonnaci, fibonnaci_cps)] 
        positive_ints)
    -- [Int] -> [Int]
    ffuzz_print (ffuzz_run 
        [
            --("Reverse", reverse_lst, reverse_lst_cps)
        ] 
        positive_list)
    -- [Int] -> Bool
    ffuzz_print (ffuzz_run 
        [
            ("Palindrome", palindrome, palindrome_cps)
        ]
        positive_list)
    -- [Int] -> Int
    ffuzz_print (ffuzz_run 
        [
            ("SumList", sum_list, sum_list_cps)
        ] 
        positive_list)
   {- print $ feq factorial factorial_cps 10
    print $ feq sum_to sum_to_cps 10
    print $ feq fibonnaci fibonnaci_cps 10
    print $ feq palindrome palindrome_cps [1,2,3]
    print $ feq reverse_lst reverse_lst_cps [1,2,3]
    print $ feq sum_list sum_list_cps [1,2,3] -}

ffuzz_print :: Show a => [(String,Bool,a)] -> IO ()
ffuzz_print results = case results of
    [] -> return ()
    (n,False,i):t -> do
        putStr "Differing result for "
        putStr n
        putStr " on input: " 
        print i
        ffuzz_print t
    _:t -> ffuzz_print t

ffuzz_run :: Eq b => [(String,a->b,a->b)] -> [a] -> [(String,Bool,a)]
ffuzz_run flst ins =
    concat $ foldl (\acc (n,f1,f2) -> foldl (\acc i -> (n, f1 i == f2 i, i) : acc) [] ins : acc) [] flst

feq :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
feq f1 f2 x = 
    f1 x == f2 x-}

-- Non-recursive functions

add :: Int -> Int -> Int
add x y = x + y


-- Recursive functions
{-
    Factorial
    Sum
    Tower of Hanoi
    Fibonacci
    List palimdrome
    List reversal
    Ackermann function
    Sum of elements in list
-}

-- Direct-Recursive functions

{-# ANN factorial "AUTO_CPS" #-}
factorial :: Int -> Int
factorial n = case n of
    0 -> 0
    1 -> 1
    n -> n * factorial (n-1)

{-# ANN sum_to "AUTO_CPS" #-}
sum_to :: Int -> Int
sum_to n = case n of
    0 -> 0
    n -> n + sum_to (n-1)

{-# ANN sum_list "AUTO_CPS" #-}
sum_list :: [Int] -> Int
sum_list lst = case lst of
    [] -> 0
    h:t -> h + sum_list t

{-# ANN fibonnaci "AUTO_CPS" #-}
fibonnaci :: Int -> Int
fibonnaci n = case n of
    0 -> 0
    1 -> 1
    n -> fibonnaci (n-1) + fibonnaci (n-2)

{-# ANN reverse_lst "AUTO_CPS" #-}
reverse_lst :: [a] -> [a]
reverse_lst lst = case lst of
    [] -> []
    h:t -> reverse_lst t ++ [h]

{-# ANN palindrome "AUTO_CPS" #-}
palindrome :: Eq a => [a] -> Bool
palindrome lst = case lst of
    [] -> True
    [a] -> True
    h:t -> case reverse t of
        h1:t1 -> (h == h1) && palindrome (reverse t1)

-- CPS-Recursive functions

factorial_cps :: Int -> Int
factorial_cps n = aux id n where
    aux c n = case n of
        0 -> c 0
        1 -> c 1
        n -> aux (\x -> c (x*n)) (n-1)

sum_to_cps :: Int -> Int
sum_to_cps n = aux id n where
    aux c n = case n of
        0 -> c 0
        n -> aux (\x -> c (x+n)) (n-1)

sum_list_cps :: [Int] -> Int
sum_list_cps lst = aux id lst where
    aux c lst = case lst of
        [] -> c 0
        h:t -> aux (\x -> c (h+x)) t

fibonnaci_cps :: Int -> Int
fibonnaci_cps n = aux id n where
    aux c n = case n of
        0 -> c 0
        1 -> c 1
        n -> aux (\x -> aux (\y -> c (x+y)) (n-2)) (n-1)

reverse_lst_cps :: [a] -> [a]
reverse_lst_cps lst = aux id lst where
    aux c lst = case lst of
        [] -> c []
        h:t -> aux (\x -> c (x++[h])) t

palindrome_cps :: Eq a => [a] -> Bool
palindrome_cps lst = aux id lst where
    aux c lst = case lst of
        [] -> c True
        [a] -> c True
        h:t -> case reverse t of
            h1:t1 -> aux (\x -> c ((h == h1) && x)) (reverse t1)