{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
class Exp x

data Lit = Lit Int

--data Add = forall x y. (Eval x, Eval y, Exp x, Exp y, Show x, Show y) => Add x y
data Add x y where
  Add :: (Exp x, Exp y) => x -> y -> Add x y

--data Minus = forall x y. (Eval x, Eval y, Exp x, Exp y, Show x, Show y) => Minus x y
data Minus x y where
  Minus :: (Exp x, Exp y) => x -> y -> Minus x y

data AnyExp = forall x. (Eval x, Exp x, Show x) => AnyExp x
  
s = [AnyExp (Add (Lit 1) (Lit 2)), AnyExp (Minus (Lit 2) (Lit 1))]

t = map (\(AnyExp x) -> eval x) s  

instance Exp Lit

instance (Exp x, Exp y) => Exp (Add x y)

instance (Exp x, Exp y) => Exp (Minus x y)

class Exp x => Eval x where
  eval :: x -> Int

instance Eval Lit where 
  eval (Lit i) = i
  
instance (Eval x, Eval y) => Eval (Add x y) where
  eval (Add x y) = (eval x) + (eval y)
  
instance (Eval x, Eval y) => Eval (Minus x y) where
  eval (Minus x y) = (eval x) - (eval y)

instance Show Lit where
  show (Lit i) = "(Lit " ++ show i ++ ")"
  
instance (Show x, Show y) => Show (Add x y) where
  show (Add x y) = "(Add " ++ show x ++ " " ++ show y ++ ")"
  
instance (Show x, Show y) => Show (Minus x y) where
  show (Minus x y) = "(Minus " ++ show x ++ " " ++ show y ++ ")"


  