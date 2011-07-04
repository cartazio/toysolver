{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Formula
  ( Complement (..)
  , Boolean (..)
  , andF
  , orF
  , RelOp (..)
  , Rel (..)
  , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
  , flipOp
  , Atom (..)
  , Formula (..)
  , pushNot
  , DNF (..)
  ) where

import qualified Data.IntSet as IS
import Expr

-- ---------------------------------------------------------------------------

infix 4 .<., .<=., .>=., .>., .==., ./=.
infixr 3 .&&.
infixr 2 .||.
infix 1 .=>. , .<=>.

class Complement a where
  notF :: a -> a

class Complement a => Boolean a where
  true, false :: a
  (.&&.), (.||.), (.=>.), (.<=>.) :: a -> a -> a
  x .=>. y = notF x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)

andF :: Boolean a => [a] -> a
andF = foldr (.&&.) true

orF :: Boolean a => [a] -> a
orF = foldr (.||.) false

-- ---------------------------------------------------------------------------

data RelOp = Lt | Le | Ge | Gt | Eql | NEq
    deriving (Show, Eq, Ord)

class Rel e r | r -> e where
  rel :: RelOp -> e -> e -> r

(.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.) :: Rel e r => e -> e -> r
a .<. b  = rel Lt  a b
a .<=. b = rel Le  a b
a .>. b  = rel Gt  a b
a .>=. b = rel Ge  a b
a .==. b = rel Eql a b
a ./=. b = rel NEq a b

flipOp :: RelOp -> RelOp 
flipOp Le = Ge
flipOp Ge = Le
flipOp Lt = Gt
flipOp Gt = Lt
flipOp Eql = Eql
flipOp NEq = NEq

-- ---------------------------------------------------------------------------

data Atom c = Rel (Expr c) RelOp (Expr c)
    deriving (Show, Eq, Ord)

instance Variables (Atom c) where
  vars (Rel a _ b) = vars a `IS.union` vars b

instance Rel (Expr c) (Atom c) where
  rel op a b = Rel a op b

-- ---------------------------------------------------------------------------

data Formula c
    = T
    | F
    | Atom (Atom c)
    | And (Formula c) (Formula c)
    | Or (Formula c) (Formula c)
    | Not (Formula c)
    | Imply (Formula c) (Formula c)
    | Equiv (Formula c) (Formula c)
    | Forall Var (Formula c)
    | Exists Var (Formula c)
    deriving (Show, Eq, Ord)

instance Variables (Formula c) where
  vars T = IS.empty
  vars F = IS.empty
  vars (Atom atom) = vars atom
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b) = vars a `IS.union` vars b
  vars (Not a) = vars a
  vars (Imply a b) = vars a `IS.union` vars b
  vars (Equiv a b) = vars a `IS.union` vars b
  vars (Forall v a) = IS.delete v (vars a)
  vars (Exists v a) = IS.delete v (vars a)

instance Complement (Formula c) where
  notF = Not

instance Boolean (Formula c) where
  true = T
  false = F
  (.&&.) = And
  (.||.) = Or
  (.=>.) = Imply
  (.<=>.) = Equiv

instance Rel (Expr c) (Formula c) where
  rel op a b = Atom $ rel op a b

pushNot :: Formula c -> Formula c
pushNot T = F
pushNot F = T
pushNot (Atom (Rel a op b)) = Atom $ Rel a op' b
  where
    op' = case op of
            Lt -> Ge
            Le -> Gt
            Ge -> Lt
            Gt -> Le
            Eql -> NEq
            NEq -> Eql
pushNot (And a b) = Or (pushNot a) (pushNot b)
pushNot (Or a b) = And (pushNot a) (pushNot b)
pushNot (Not a) = a
pushNot (Imply a b) = And a (pushNot b)
pushNot (Equiv a b) = Or (And a (pushNot b)) (And b (pushNot a))
pushNot (Forall v a) = Exists v (pushNot a)
pushNot (Exists v a) = Forall v (pushNot a)

-- | Disjunctive normal form
newtype DNF lit = DNF{ unDNF :: [[lit]] } deriving (Show)

instance Complement lit => Complement (DNF lit) where
  notF (DNF xs) = DNF . sequence . map (map notF) $ xs

instance Complement lit => Boolean (DNF lit) where
  true = DNF [[]]
  false = DNF []
  DNF xs .&&. DNF ys = DNF [x++y | x<-xs, y<-ys]
  DNF xs .||. DNF ys = DNF (xs++ys)