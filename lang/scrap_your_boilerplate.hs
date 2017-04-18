--Scrap Your Boilerplate: A Practical Design Pattern for Generic Programming

{-# LANGUAGE Rank2Types #-}

import Data.Typeable

mkT :: (Typeable a, Typeable b) => (b -> b) -> a -> a
mkT f = case cast f of
          Just g -> g
          Nothing -> id

mkQ :: (Typeable a, Typeable b) => r -> (b -> r) -> a -> r
mkQ r q a = case cast a of
              Just b -> q b
              Nothing -> r


class Typeable a => Term a where
  gmapT :: (forall b. Term b => b -> b) -> a -> a
  gmapQ :: (forall b. Term b => b -> r) -> a -> [r]
  gmapM :: Monad m => (forall b. Term b => b -> m b) -> a -> m a
  gfoldl :: (forall a b. Term a => w (a -> b) -> a -> w b) 
         -> (forall g. g -> w g) 
         -> a -> w a

instance Term Bool where
  gmapT f x = x
  gmapQ f x = []
  gmapM f x = do x' <- f x
                 return x'
  gfoldl k z x = z id `k` x
  
instance Term Int where
  gmapT f x = x
  gmapQ f x = []
  gmapM f x = do x' <- f x
                 return x'
  gfoldl k z x = z id `k` x
  
instance Term a => Term [a] where
  gmapT f [] = []
  gmapT f (x:xs) = f x : f xs
  gmapQ f [] = []
  gmapQ f (x:xs) = [f x, f xs]
  gmapM f [] = return []
  gmapM f (x:xs) = do x' <- f x
                      xs' <- f xs
                      return (x':xs')
  gfoldl k z x = z id `k` x
  
-- bottom-up
everywhere :: Term a => (forall b. Term b => b -> b) -> a -> a
everywhere f x = f (gmapT (everywhere f) x)

-- top-down
everywhere' :: Term a => (forall b. Term b => b -> b) -> a -> a
everywhere' f x = gmapT (everywhere' f) (f x)

-- Summarise all nodes in top-down, left-to-right
everything :: Term a => (r -> r -> r) -> (forall a. Term a => a -> r) -> a -> r
everything k f x = foldl k (f x) (gmapQ (everything k f) x)
