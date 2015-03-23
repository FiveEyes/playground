-- http://conal.net/papers/push-pull-frp/push-pull-frp.pdf

import Control.Monad
import Control.Applicative
import Data.Monoid

type Time = Double
infinity = 1.0 / 0.0::Time
nagInfinity = -1.0 / 0.0 :: Time

type B a = Time -> a
type E a = [(Time, a)]

newtype Behavior a = 
  Behavior {
    at :: B a
  }
  
newtype Event a = 
  Event {
    occs :: E a
  }
  
time::Behavior Time
time = Behavior id

instance Functor Behavior where
  fmap f ba = Behavior $ fmap f (at ba)
  
instance Applicative Behavior where
  pure a = Behavior (const a) 
  (<*>) fab fa = Behavior $ (at fab) <*> (at fa)   
  
lift2 :: (a1 -> a2 -> b) -> Behavior a1 -> Behavior a2 -> Behavior b
lift2 f ba1 ba2 = f <$> ba1 <*> ba2

lift3 :: (a1 -> a2 -> a3 -> b) -> Behavior a1 -> Behavior a2 -> Behavior a3 -> Behavior b
lift3 f ba1 ba2 ba3 = (lift2 f ba1 ba2) <*> ba3

merge :: E a -> E a -> E a
merge [] rs = rs
merge ls [] = ls
merge ((t0,a0):xs) ((t1,a1):ys)
  | t0 <= t1 = (t0,a0):(merge xs ((t1,a1):ys))
  | otherwise = (t1,a1):(merge ((t0,a0):xs) ys)

instance Monoid (Event a) where
  mempty = Event []
  mappend l r = Event $ merge (occs l) (occs r)
  
instance Functor Event where
  fmap f ea = Event $ map (\(t, a) -> (t, f a)) (occs ea)
 
delayOccs :: (Time, Event a) -> E a
delayOccs (t, e) = [(max t ta, a) | (ta, a) <- occs e]
 
joinE :: Event (Event a) -> Event a
joinE ee = Event $ foldr merge [] $ map delayOccs (occs ee)

instance Monad Event where
  return a = Event [(nagInfinity, a)]
  (>>=) ea f = joinE $ fmap f ea
  
instance Applicative Event where
  pure = return
  (<*>) = ap

