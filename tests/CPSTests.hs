{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}


module CPSTests where

import GHC.List hiding (concat)
import Prelude hiding (foldl)
--import System.Random
  
--  print $ take 10 (randomRs ('a', 'z') g)

test :: IO ()
test = do
    --g <- getStdGen
    --let meme = take 10 (randoms g :: [Int])
    ffuzz_print (ffuzz_run [("Factorial", factorial, factorial_cps)] [1, 10, 30])
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
    f1 x == f2 x

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

--{-# ANN factorial "AUTO_CPS" #-}
factorial :: Int -> Int
factorial n = case n of
    0 -> 0
    1 -> 1
    n -> n * factorial (n-1)

sum_to :: Int -> Int
sum_to n = case n of
    0 -> 0
    n -> n + sum_to (n-1)

sum_list :: [Int] -> Int
sum_list lst = case lst of
    [] -> 0
    h:t -> h + sum_list t

fibonnaci :: Int -> Int
fibonnaci n = case n of
    0 -> 0
    1 -> 1
    n -> fibonnaci (n-1) + fibonnaci (n-2)

--{-# ANN reverse_lst "AUTO_CPS" #-}
reverse_lst :: [a] -> [a]
reverse_lst lst = case lst of
    [] -> []
    h:t -> reverse_lst t ++ [h]

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