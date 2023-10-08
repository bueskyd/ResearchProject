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
