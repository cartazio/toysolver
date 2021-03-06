{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.PB2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.PB2LP
  ( convert
  , convertWBO
  ) where

import Data.Array.IArray
import Data.List
import Data.Maybe
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Text.PBFile as PBFile
import qualified Text.LPFile as LPFile
import qualified SAT.Types as SAT

convert :: PBFile.Formula -> (LPFile.LP, Map LPFile.Var Rational -> SAT.Model)
convert formula@(obj, cs) = (lp, mtrans (PBFile.pbNumVars formula))
  where
    lp = LPFile.LP
      { LPFile.variables = vs2
      , LPFile.dir = dir
      , LPFile.objectiveFunction = (Nothing, obj2)
      , LPFile.constraints = cs2
      , LPFile.sosConstraints = []
      , LPFile.userCuts = []
      , LPFile.varInfo = Map.fromAscList
          [ ( v
            , LPFile.VarInfo
              { LPFile.varType   = LPFile.IntegerVariable
              , LPFile.varBounds = (LPFile.Finite 0, LPFile.Finite 1)
              }
            )
          | v <- Set.toAscList vs2
          ]
      }

    vs1 = collectVariables formula
    vs2 = (Set.fromList . map convVar . IntSet.toList) $ vs1

    (dir,obj2) =
      case obj of
        Just obj' -> (LPFile.OptMin, convExpr obj')
        Nothing   -> (LPFile.OptMin, convExpr [])

    cs2 = do
      (lhs,op,rhs) <- cs
      let op2 = case op of
                  PBFile.Ge -> LPFile.Ge
                  PBFile.Eq -> LPFile.Eql
          lhs2 = convExpr lhs
          lhs3a = [t | t@(LPFile.Term _ (_:_)) <- lhs2]
          lhs3b = sum [c | LPFile.Term c [] <- lhs2]
      return $ LPFile.Constraint
        { LPFile.constrLabel     = Nothing
        , LPFile.constrIndicator = Nothing
        , LPFile.constrIsLazy    = False
        , LPFile.constrBody      = (lhs3a, op2, fromIntegral rhs - lhs3b)
        }

convExpr :: PBFile.Sum -> LPFile.Expr
convExpr [] = [LPFile.Term 0 [LPFile.toVar "x1"]]
convExpr s = concatMap g2 s
  where
    g2 :: PBFile.WeightedTerm -> LPFile.Expr
    g2 (w, tm) = foldl' prodE [LPFile.Term (fromIntegral w) []] (map g3 tm)

    g3 :: PBFile.Lit -> LPFile.Expr
    g3 x
      | x > 0     = [LPFile.Term 1 [convVar x]]
      | otherwise = [LPFile.Term 1 [], LPFile.Term (-1) [convVar (abs x)]]

    prodE :: LPFile.Expr -> LPFile.Expr -> LPFile.Expr
    prodE e1 e2 = [prodT t1 t2 | t1 <- e1, t2 <- e2]

    prodT :: LPFile.Term -> LPFile.Term -> LPFile.Term
    prodT (LPFile.Term c1 vs1) (LPFile.Term c2 vs2) = LPFile.Term (c1*c2) (vs1++vs2)

convVar :: PBFile.Var -> LPFile.Var
convVar x = LPFile.toVar ("x" ++ show x)

collectVariables :: PBFile.Formula -> IntSet
collectVariables (obj, cs) = IntSet.unions $ maybe IntSet.empty f obj : [f s | (s,_,_) <- cs]
  where
    f :: PBFile.Sum -> IntSet
    f xs = IntSet.fromList $ do
      (_,ts) <- xs
      lit <- ts
      return $ abs lit

convertWBO :: Bool -> PBFile.SoftFormula -> (LPFile.LP, Map LPFile.Var Rational -> SAT.Model)
convertWBO useIndicator formula@(top, cs) = (lp, mtrans (PBFile.wboNumVars formula))
  where
    lp = LPFile.LP
      { LPFile.variables = vs2
      , LPFile.dir = LPFile.OptMin
      , LPFile.objectiveFunction = (Nothing, obj2)
      , LPFile.constraints = topConstr ++ map snd cs2
      , LPFile.sosConstraints = []
      , LPFile.userCuts = []
      , LPFile.varInfo = Map.fromAscList
          [ ( v
            , LPFile.VarInfo
              { LPFile.varType   = LPFile.IntegerVariable
              , LPFile.varBounds = (LPFile.Finite 0, LPFile.Finite 1)
              }
            )
          | v <- Set.toAscList vs2
          ]
      }

    vs1 = collectVariablesWBO formula
    vs2 = ((Set.fromList . map convVar . IntSet.toList) $ vs1) `Set.union` vs3
    vs3 = Set.fromList [v | (ts, _) <- cs2, (_, v) <- ts]

    obj2 = [LPFile.Term (fromIntegral w) [v] | (ts, _) <- cs2, (w, v) <- ts]

    topConstr :: [LPFile.Constraint]
    topConstr = 
     case top of
       Nothing -> []
       Just t ->
          [ LPFile.Constraint
            { LPFile.constrLabel     = Nothing
            , LPFile.constrIndicator = Nothing
            , LPFile.constrIsLazy    = False
            , LPFile.constrBody      = (obj2, LPFile.Le, fromInteger t - 1)
            }
          ]

    cs2 :: [([(Integer, LPFile.Var)], LPFile.Constraint)]
    cs2 = do
      (n, (w, (lhs,op,rhs))) <- zip [(0::Int)..] cs
      let 
          lhs2 = convExpr lhs
          lhs3 = [t | t@(LPFile.Term _ (_:_)) <- lhs2]
          rhs3 = fromIntegral rhs - sum [c | LPFile.Term c [] <- lhs2]
          v = LPFile.toVar ("r" ++ show n)
          (ts,ind) =
            case w of
              Nothing -> ([], Nothing)
              Just w2 -> ([(w2,v)], Just (v,0))
      if isNothing w || useIndicator then do
         let op2 =
               case op of
                 PBFile.Ge -> LPFile.Ge
                 PBFile.Eq -> LPFile.Eql
             c = LPFile.Constraint
                 { LPFile.constrLabel     = Nothing
                 , LPFile.constrIndicator = ind
                 , LPFile.constrIsLazy    = False
                 , LPFile.constrBody      = (lhs3, op2, rhs3)
                 }
         return (ts, c)
       else do
         let (lhsGE,rhsGE) = relaxGE v (lhs3,rhs3)
             c1 = LPFile.Constraint
                  { LPFile.constrLabel     = Nothing
                  , LPFile.constrIndicator = Nothing
                  , LPFile.constrIsLazy    = False
                  , LPFile.constrBody      = (lhsGE, LPFile.Ge, rhsGE)
                  }
         case op of
           PBFile.Ge -> do
             return (ts, c1)
           PBFile.Eq -> do
             let (lhsLE,rhsLE) = relaxLE v (lhs3,rhs3)
                 c2 = LPFile.Constraint
                      { LPFile.constrLabel     = Nothing
                      , LPFile.constrIndicator = Nothing
                      , LPFile.constrIsLazy    = False
                      , LPFile.constrBody      = (lhsLE, LPFile.Le, rhsLE)
                      }
             [ (ts, c1), ([], c2) ]

relaxGE :: LPFile.Var -> (LPFile.Expr, Rational) -> (LPFile.Expr, Rational)
relaxGE v (lhs, rhs) = (LPFile.Term (rhs - lhs_lb) [v] : lhs, rhs)
  where
    lhs_lb = sum [min c 0 | LPFile.Term c _ <- lhs]

relaxLE :: LPFile.Var -> (LPFile.Expr, Rational) -> (LPFile.Expr, Rational)
relaxLE v (lhs, rhs) = (LPFile.Term (rhs - lhs_ub) [v] : lhs, rhs)
  where
    lhs_ub = sum [max c 0 | LPFile.Term c _ <- lhs]

collectVariablesWBO :: PBFile.SoftFormula -> IntSet
collectVariablesWBO (_top, cs) = IntSet.unions [f s | (_,(s,_,_)) <- cs]
  where
    f :: PBFile.Sum -> IntSet
    f xs = IntSet.fromList $ do
      (_,ts) <- xs
      lit <- ts
      return $ abs lit

mtrans :: Int -> Map LPFile.Var Rational -> SAT.Model
mtrans nvar m =
  array (1, nvar)
    [　(i, val)
    | i <- [1 .. nvar]
    , let val =
            case m Map.! (convVar i) of
              0  -> False
              1  -> True
              v0 -> error (show v0 ++ " is neither 0 nor 1")
    ]
