module Main where

main :: IO ()
main = mapM_ (print . fib) $ take 10 $ iterate (1+) 0

--manyArgs :: Int -> Float -> Bool -> String -> Bool
--manyArgs n f b s = False

{-foo :: Int -> Int -> Int
foo a b = a + b + a-}

{-bar :: Int -> Int
bar 0 = 0
bar n = n + bar (n - 1)-}

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

{-fibC :: Int -> Int
fibC n = aux n id where
    aux n c = case n of
        0 -> c 0
        1 -> c 1
        n -> aux (n - 1) (\x -> aux (n - 2) (\y -> c (x + y)))-}

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