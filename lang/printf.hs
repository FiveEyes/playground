--using GADTs to remove the declaration of inner
{-# LANGUAGE GADTs #-}

import Text.Printf

solve :: Int -> Int -> IO ()
solve x y = inner y
  where
  --inner :: Int -> IO ()
  inner 0 = return ()
  inner y = do
	printf "%d %d\n" x y
	inner (y - 1)
