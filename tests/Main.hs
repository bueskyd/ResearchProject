module Main where

main :: IO ()
main = putStrLn "Hello, World!"

foo :: Int -> Int -> Int
foo a b = a + b + a

bar :: Int -> Int
bar 0 = 0
bar n = n + bar (n - 1)

barA :: Int -> Int-> Int
barA 0 acc = acc
barA n acc = barA (n - 1) (acc + n)

{-# ANN barT (Just "Hello") #-}
{-# ANN foo (Just "Hello") #-}
{-# ANN barA (Just "Hello") #-}
barT :: Int -> Int
barT n = aux n id
    where
        aux 0 c = c 0
        aux n c = aux (n - 1) (\x -> c $ n + x)
        
tailRec0 :: Int -> Int
tailRec0 0 = 0
tailRec0 1 = 1
tailRec0 n = tailRec1 (n - 1)

tailRec1 :: Int -> Int
tailRec1 0 = 0
tailRec1 1 = 1
tailRec1 n = tailRec0 (n - 2)

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
