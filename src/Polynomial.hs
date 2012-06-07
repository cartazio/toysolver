{-# LANGUAGE ScopedTypeVariables #-}

{-
メモ

Monomial order
http://en.wikipedia.org/wiki/Monomial_order

Gröbner basis
http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis

グレブナー基底
http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC

Gröbner Bases and Buchberger’s Algorithm
http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf

Rubyでの実装
http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html

HaskellではDoConに実装があり
http://www.haskell.org/docon/
GBasisモジュール
-}

module Polynomial
  (
  -- * Polynomial type
    Var
  , Polynomial

  -- * Conversion
  , var
  , constant
  , fromMonomials
  , fromMonomial
  , terms

  -- * Query
  , leadingTerm
  , deg

  -- * Operations
  , deriv

  -- * Monomial
  , Monomial
  , monomialDegree
  , monomialProd
  , monomialDivisible
  , monomialDiv

  -- * Monic monomial
  , MonicMonomial
  , mmOne
  , mmDegree
  , mmProd
  , mmDivisible
  , mmDiv
  , mmLCM
  , mmGCD

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Gröbner basis
  , buchberger
  , reduce
  , spolynomial
  , reduceGBase

  -- * Utility functions
  , showPoly
  ) where

import Prelude hiding (lex)
import Control.Monad
import Data.Function
import Data.List
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMultiSet as IMS

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

type Var = Int

newtype Polynomial k = Polynomial (Map.Map MonicMonomial k)
  deriving (Eq, Ord, Show)

instance (Eq k, Num k) => Num (Polynomial k) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmProd` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = normalize $ Polynomial $ Map.singleton mmOne (fromInteger x)

normalize :: (Eq k, Num k) => Polynomial k -> Polynomial k
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

var :: (Eq k, Num k) => Var -> Polynomial k
var x = Polynomial (Map.singleton (IMS.singleton x) 1)

constant :: (Eq k, Num k) => k -> Polynomial k
constant c = normalize $ Polynomial (Map.singleton mmOne c)

fromMonomials :: (Eq k, Num k) => [Monomial k] -> Polynomial k
fromMonomials = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromMonomial :: (Eq k, Num k) => Monomial k -> Polynomial k
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

terms :: Polynomial k -> [Monomial k]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

leadingTerm :: (Eq k, Num k) => MonomialOrder -> Polynomial k -> Monomial k
leadingTerm cmp p =
  case terms p of
    [] -> (0, mmOne) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

deg :: Polynomial k -> Integer
deg = maximum . map monomialDegree . terms

deriv :: (Eq k, Num k) => Polynomial k -> Var -> Polynomial k
deriv p x = sum $ do
  (c,xs) <- terms p
  let n = IMS.occur x xs
  if n == 0
    then return 0
    else return $ fromMonomial (c * fromIntegral n, IMS.delete x xs)

showPoly :: (Eq k, Ord k, Num k, Show k) => Polynomial k -> String
showPoly p = intercalate " + " [f c xs | (c,xs) <- sortBy (flip grlex `on` snd) $ terms p]
  where
    f c xs = (intercalate "*" ([showsPrec 8 c "" | c /= 1 || IMS.null xs] ++ [g x n | (x,n) <- IMS.toOccurList xs]))
    g x 1 = "x" ++ show x
    g x n = "x" ++ show x ++ "^" ++ show n

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

type Monomial k = (k, MonicMonomial)

monomialDegree :: Monomial k -> Integer
monomialDegree (_,xs) = mmDegree xs

monomialProd :: Num k => Monomial k -> Monomial k -> Monomial k
monomialProd (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmProd` xs2)

monomialDivisible :: Fractional k => Monomial k -> Monomial k -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = mmDivisible xs1 xs2

monomialDiv :: Fractional k => Monomial k -> Monomial k -> Monomial k
monomialDiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mmDiv` xs2)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

type MonicMonomial = IMS.IntMultiSet

mmDegree :: MonicMonomial -> Integer
mmDegree = sum . map (fromIntegral . snd) . IMS.toOccurList

mmOne :: MonicMonomial
mmOne = IMS.empty

mmProd :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmProd xs1 xs2 = xs1 `IMS.union` xs2

mmDivisible :: MonicMonomial -> MonicMonomial -> Bool
mmDivisible xs1 xs2 = xs2 `IMS.isSubsetOf` xs1

mmDiv :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmDiv xs1 xs2 = xs1 `IMS.difference` xs2

mmLCM :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmLCM = IMS.maxUnion

mmGCD :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmGCD m1 m2 = IMS.fromDistinctAscOccurList xs
  where
    xs = f (IMS.toAscOccurList m1) (IMS.toAscOccurList m2)
    f [] _ = []
    f _ [] = []
    f xxs1@((x1,c1):xs1) xxs2@((x2,c2):xs2) =
      case compare x1 x2 of
        EQ -> (x1, min c1 c2) : f xs1 xs2
        LT -> f xs1 xxs2
        GT -> f xxs1 xs2

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder = MonicMonomial -> MonicMonomial -> Ordering

-- | Lexicographic order
lex :: MonomialOrder
lex xs1 xs2 = go (IMS.toAscOccurList xs1) (IMS.toAscOccurList xs2)
  where
    go [] [] = EQ
    go [] _  = LT -- = cmpare 0 n2
    go _ []  = GT -- = cmpare n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- | Reverse lexicographic order
-- Note that revlex is NOT a monomial order.
revlex :: MonicMonomial -> MonicMonomial -> Ordering
revlex xs1 xs2 = go (reverse (IMS.toAscOccurList xs1)) (reverse (IMS.toAscOccurList xs2))
  where
    go [] [] = EQ
    go [] _  = GT -- = cmp 0 n2
    go _ []  = LT -- = cmp n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = cmp 0 n2
        GT -> LT -- = cmp n1 0
        EQ -> cmp n1 n2 `mappend` go xs1 xs2
    cmp n1 n2 = compare n2 n1

-- | graded lexicographic order
grlex :: MonomialOrder
grlex = (compare `on` mmDegree) `mappend` lex

-- | graded reverse lexicographic order
grevlex :: MonomialOrder
grevlex = (compare `on` mmDegree) `mappend` revlex

{--------------------------------------------------------------------
  Gröbner basis
--------------------------------------------------------------------}

-- | Multivariate division algorithm
reduce  :: (Eq k, Fractional k) => MonomialOrder -> Polynomial k -> [Polynomial k] -> Polynomial k
reduce cmp p fs = go p
  where
    ls = [(leadingTerm cmp f, f) | f <- fs]
    go g = if null xs then g else go (head xs)
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (a,f) <- ls
          h <- ms
          guard $ monomialDivisible h a
          return (g - fromMonomial (monomialDiv h a) * f)

spolynomial :: (Eq k, Fractional k) => MonomialOrder -> Polynomial k -> Polynomial k -> Polynomial k
spolynomial cmp f g =
      fromMonomial ((1,xs) `monomialDiv` (c1,xs1)) * f
    - fromMonomial ((1,xs) `monomialDiv` (c2,xs2)) * g
  where
    xs = mmLCM xs1 xs2
    (c1, xs1) = leadingTerm cmp f
    (c2, xs2) = leadingTerm cmp g

buchberger :: forall k. (Eq k, Fractional k, Ord k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
buchberger cmp fs = reduceGBase cmp $ go fs (pairs fs)
  where  
    go :: [Polynomial k] -> [(Polynomial k, Polynomial k)] -> [Polynomial k]
    go gs [] = gs
    go gs ((fi,fj):ps)
      | r == 0    = go gs ps
      | otherwise = go (r:gs) ([(r,g) | g <- gs] ++ ps)
      where
        spoly = spolynomial cmp fi fj
        r = reduce cmp spoly gs

reduceGBase :: forall k. (Eq k, Ord k, Fractional k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
reduceGBase cmp ps = Set.toList $ Set.fromList $ do
  (p,qs) <- choose ps
  let q = reduce cmp p qs
  guard $ q /= 0
  let (c,_) = leadingTerm cmp q
  return $ constant (1/c) * q

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs

choose :: [a] -> [(a,[a])]
choose [] = []
choose (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- choose xs]
