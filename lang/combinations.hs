-- memoization
import qualified Data.Vector as V

c :: Int -> Int -> Integer
c n m = (cn n) !! m
  where 
  cn 0 = 1:(repeat 0)
  cn n = let s = (cn $ n - 1) in zipWith (+) (0:s) s
   
getComp :: Int -> Int -> V.Vector (V.Vector Integer)
getComp n m = c
  where
  c = V.fromList [ V.fromList [ f i j | j <- [0..min i m]] | i <- [0..n]]
    where
    f x y | y == 0    = 1
          | x == y    = 1
          | otherwise = c V.! (x-1) V.! y + c V.! (x-1) V.! (y-1)
		  
comp n m = getComp 100 100 V.! n V.! m