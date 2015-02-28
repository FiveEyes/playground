--read n and a_1, ..., a_n, then sort them.

import Data.Char
import Control.Monad

str2Int = read :: String->Int

qsort [] = []
qsort (x:xs) = qsort (filter (< x) xs) ++ [x] ++ qsort (filter (>= x) xs)


--contentsSort :: [Int] -> [Int]
--contentsSort [] = []
--contentsSort (n:xs) = qsort (take n xs) ++ contentsSort (drop n xs)

--main = do
--  contents <- getContents
--  ls <- return $ contentsSort (map str2Int (lines contents))
--  mapM_ print ls

main = forever $ do
  n <- readLn :: IO Int
  arr <- sequence $ replicate n getLine
  mapM_ print (qsort $ map str2Int arr)
