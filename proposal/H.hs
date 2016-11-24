module H where

import System.Microtimer

-- square :: Integer -> Integer
-- square n = n * n

pow :: Integer -> Integer -> Integer
pow a 0 = 1
pow a b = a * pow a (b-1)

pow' :: Integer -> Integer -> Integer
pow' a 0 = 1
pow' a 1 = a
pow' a b | even b = pow' (a * a) (b `div` 2)
pow' a b | odd b = a * pow' a (b-1)

timing f a b =
  do s <- time_ $ print (f a b)
     putStrLn (formatSeconds s)

-- timing pow 2 10000
-- 27.31109 ms

-- timing pow' 2 10000
-- 11.72614 ms

