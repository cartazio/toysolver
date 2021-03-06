{-# LANGUAGE BangPatterns #-}
module SAT.Types
  (
  -- * Variable
    Var
  , VarSet
  , VarMap
  , validVar

  -- * Model
  , Model

  -- * Literal
  , Lit
  , LitSet
  , LitMap
  , litUndef
  , validLit
  , literal
  , litNot
  , litVar
  , litPolarity
  , evalLit

  -- * Clause
  , Clause
  , normalizeClause
  , clauseSubsume

  -- * Cardinality Constraint
  , AtLeast
  , normalizeAtLeast

  -- * Pseudo Boolean Constraint
  , PBLinTerm
  , PBLinSum
  , PBLinAtLeast
  , PBLinExactly
  , normalizePBSum
  , normalizePBAtLeast
  , normalizePBExactly
  , cutResolve
  , cardinalityReduction
  , negatePBAtLeast
  , pbEval
  , pbLowerBound
  , pbUpperBound
  , pbSubsume
  ) where

import Control.Monad
import Control.Exception
import Data.Array.Unboxed
import Data.Ord
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarSet = IntSet
type VarMap = IntMap

{-# INLINE validVar #-}
validVar :: Var -> Bool
validVar v = v > 0

-- | A model is represented as a mapping from variables to its values.
type Model = UArray Var Bool

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

{-# INLINE litUndef #-}
litUndef :: Lit
litUndef = 0

type LitSet = IntSet
type LitMap = IntMap

{-# INLINE validLit #-}
validLit :: Lit -> Bool
validLit l = l /= 0

{-# INLINE literal #-}
-- | Construct a literal from a variable and its polarity.
-- 'True' (resp 'False') means positive (resp. negative) literal.
literal :: Var  -- ^ variable
        -> Bool -- ^ polarity
        -> Lit
literal v polarity =
  assert (validVar v) $ if polarity then v else litNot v

{-# INLINE litNot #-}
-- | Negation of the 'Lit'.
litNot :: Lit -> Lit
litNot l = assert (validLit l) $ negate l

{-# INLINE litVar #-}
-- | Underlying variable of the 'Lit'
litVar :: Lit -> Var
litVar l = assert (validLit l) $ abs l

{-# INLINE litPolarity #-}
-- | Polarity of the 'Lit'.
-- 'True' means positive literal and 'False' means negative literal.
litPolarity :: Lit -> Bool
litPolarity l = assert (validLit l) $ l > 0

{-# INLINE evalLit #-}
evalLit :: Model -> Lit -> Bool
evalLit m l = if l > 0 then m ! l else not (m ! abs l)

-- | Disjunction of 'Lit'.
type Clause = [Lit]

-- | Normalizing clause
--
-- 'Nothing' if the clause is trivially true.
normalizeClause :: Clause -> Maybe Clause
normalizeClause lits = assert (IntSet.size ys `mod` 2 == 0) $
  if IntSet.null ys
    then Just (IntSet.toList xs)
    else Nothing
  where
    xs = IntSet.fromList lits
    ys = xs `IntSet.intersection` (IntSet.map litNot xs)

clauseSubsume :: Clause -> Clause -> Bool
clauseSubsume cl1 cl2 = cl1' `IntSet.isSubsetOf` cl2'
  where
    cl1' = IntSet.fromList cl1
    cl2' = IntSet.fromList cl2

type AtLeast = ([Lit], Int)

normalizeAtLeast :: AtLeast -> AtLeast
normalizeAtLeast (lits,n) = assert (IntSet.size ys `mod` 2 == 0) $
   (IntSet.toList lits', n')
   where
     xs = IntSet.fromList lits
     ys = xs `IntSet.intersection` (IntSet.map litNot xs)
     lits' = xs `IntSet.difference` ys
     n' = n - (IntSet.size ys `div` 2)

type PBLinTerm = (Integer, Lit)
type PBLinSum = [PBLinTerm]
type PBLinAtLeast = (PBLinSum, Integer)
type PBLinExactly = (PBLinSum, Integer)

-- | normalizing PB term of the form /c1 x1 + c2 x2 ... cn xn + c/ into
-- /d1 x1 + d2 x2 ... dm xm + d/ where d1,...,dm ≥ 1.
normalizePBSum :: (PBLinSum, Integer) -> (PBLinSum, Integer)
normalizePBSum = step2 . step1
  where
    -- 同じ変数が複数回現れないように、一度全部 @v@ に統一。
    step1 :: (PBLinSum, Integer) -> (PBLinSum, Integer)
    step1 (xs,n) =
      case loop (IntMap.empty,n) xs of
        (ys,n') -> ([(c,v) | (v,c) <- IntMap.toList ys], n')
      where
        loop :: (VarMap Integer, Integer) -> PBLinSum -> (VarMap Integer, Integer)
        loop (ys,m) [] = (ys,m)
        loop (ys,m) ((c,l):zs) =
          if litPolarity l
            then loop (IntMap.insertWith (+) l c ys, m) zs
            else loop (IntMap.insertWith (+) (litNot l) (negate c) ys, m+c) zs

    -- 係数が0のものも取り除き、係数が負のリテラルを反転することで、
    -- 係数が正になるようにする。
    step2 :: (PBLinSum, Integer) -> (PBLinSum, Integer)
    step2 (xs,n) = loop ([],n) xs
      where
        loop (ys,m) [] = (ys,m)
        loop (ys,m) (t@(c,l):zs)
          | c == 0 = loop (ys,m) zs
          | c < 0  = loop ((negate c,litNot l):ys, m+c) zs
          | otherwise = loop (t:ys,m) zs

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn >= b/.
normalizePBAtLeast :: PBLinAtLeast -> PBLinAtLeast
normalizePBAtLeast a =
　case step1 a of
    (xs,n)
      | n > 0     -> step3 (saturate n xs, n)
      | otherwise -> ([], 0) -- trivially true
  where
    step1 :: PBLinAtLeast -> PBLinAtLeast
    step1 (xs,n) =
      case normalizePBSum (xs,-n) of
        (ys,m) -> (ys, -m)

    -- degree以上の係数はそこで抑える。
    saturate :: Integer -> PBLinSum -> PBLinSum
    saturate n xs = [assert (c>0) (min n c, l) | (c,l) <- xs]

    -- omega test と同様の係数の gcd による単純化
    step3 :: PBLinAtLeast -> PBLinAtLeast
    step3 ([],n) = ([],n)
    step3 (xs,n) = ([(c `div` d, l) | (c,l) <- xs], (n+d-1) `div` d)
      where
        d = foldl1' gcd [c | (c,_) <- xs]

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn = b/.
normalizePBExactly :: PBLinExactly -> PBLinExactly
normalizePBExactly a =
　case step1 $ a of
    (xs,n)
      | n >= 0    -> step2 (xs, n)
      | otherwise -> ([], 1) -- false
  where
    step1 :: PBLinExactly -> PBLinExactly
    step1 (xs,n) =
      case normalizePBSum (xs,-n) of
        (ys,m) -> (ys, -m)

    -- omega test と同様の係数の gcd による単純化
    step2 :: PBLinExactly -> PBLinExactly
    step2 ([],n) = ([],n)
    step2 (xs,n)
      | n `mod` d == 0 = ([(c `div` d, l) | (c,l) <- xs], n `div` d)
      | otherwise      = ([], 1) -- false
      where
        d = foldl1' gcd [c | (c,_) <- xs]

cutResolve :: PBLinAtLeast -> PBLinAtLeast -> Var -> PBLinAtLeast
cutResolve (lhs1,rhs1) (lhs2,rhs2) v = assert (l1 == litNot l2) $ normalizePBAtLeast pb
  where
    (c1,l1) = head [(c,l) | (c,l) <- lhs1, litVar l == v]
    (c2,l2) = head [(c,l) | (c,l) <- lhs2, litVar l == v]
    g = gcd c1 c2
    s1 = c2 `div` g
    s2 = c1 `div` g
    pb = ([(s1*c,l) | (c,l) <- lhs1] ++ [(s2*c,l) | (c,l) <- lhs2], s1*rhs1 + s2 * rhs2)

cardinalityReduction :: PBLinAtLeast -> AtLeast
cardinalityReduction (lhs,rhs) = (ls, rhs')
  where
    rhs' = go1 0 0 (sortBy (flip (comparing fst)) lhs)

    go1 !s !k ((a,_):ts)
      | s < rhs   = go1 (s+a) (k+1) ts
      | otherwise = k
    go1 _ _ [] = error "cardinalityReduction: should not happen"

    ls = go2 (minimum (rhs : map (subtract 1 . fst) lhs)) (sortBy (comparing fst) lhs)

    go2 !guard' ((a,_) : ts)
      | a - 1 < guard' = go2 (guard' - a) ts
      | otherwise      = map snd ts
    go2 _ [] = error "cardinalityReduction: should not happen"

negatePBAtLeast :: PBLinAtLeast -> PBLinAtLeast
negatePBAtLeast (xs, rhs) = ([(-c,lit) | (c,lit)<-xs] , -rhs + 1)

pbEval :: Model -> PBLinSum -> Integer
pbEval m xs = sum [c | (c,lit) <- xs, evalLit m lit]

pbLowerBound :: PBLinSum -> Integer
pbLowerBound xs = sum [if c < 0 then c else 0 | (c,_) <- xs]

pbUpperBound :: PBLinSum -> Integer
pbUpperBound xs = sum [if c > 0 then c else 0 | (c,_) <- xs]

-- (Σi ci li ≥ rhs1) subsumes (Σi di li ≥ rhs2) iff rhs1≥rhs2 and di≥ci for all i.
pbSubsume :: PBLinAtLeast -> PBLinAtLeast -> Bool
pbSubsume (lhs1,rhs1) (lhs2,rhs2) =
  rhs1 >= rhs2 && and [di >= ci | (ci,li) <- lhs1, let di = IntMap.findWithDefault 0 li lhs2']
  where
    lhs2' = IntMap.fromList [(l,c) | (c,l) <- lhs2]
