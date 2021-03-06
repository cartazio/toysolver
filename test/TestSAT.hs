{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import qualified Data.Set as Set
import qualified Data.IntSet as IS
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import SAT
import SAT.Types
import qualified SAT.TseitinEncoder as Tseitin
import SAT.TseitinEncoder (Formula (..))
import qualified SAT.MUS as MUS
import qualified SAT.CAMUS as CAMUS

-- should be SAT
case_solve_SAT :: IO ()
case_solve_SAT = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver
  ret @?= True

-- shuld be UNSAT
case_solve_UNSAT :: IO ()
case_solve_UNSAT = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x2 or not x2
  ret <- solve solver
  ret @?= False

-- top level でいきなり矛盾
case_root_inconsistent :: IO ()
case_root_inconsistent = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [literal x1 True]
  addClause solver [literal x1 False]
  ret <- solve solver -- unsat
  ret @?= False

-- incremental に制約を追加
case_incremental_solving :: IO ()
case_incremental_solving = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver -- sat
  ret @?= True

  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  ret <- solve solver -- unsat
  ret @?= False

-- 制約なし
case_empty_constraint :: IO ()
case_empty_constraint = do
  solver <- newSolver
  ret <- solve solver
  ret @?= True

-- 空の節
case_empty_claue :: IO ()
case_empty_claue = do
  solver <- newSolver
  addClause solver []
  ret <- solve solver
  ret @?= False

-- 自明に真な節
case_excluded_middle_claue :: IO ()
case_excluded_middle_claue = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1, -x1] -- x1 or not x1
  ret <- solve solver
  ret @?= True

-- 冗長な節
case_redundant_clause :: IO ()
case_redundant_clause = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1,x1] -- x1 or x1
  ret <- solve solver
  ret @?= True

case_instantiateClause :: IO ()
case_instantiateClause = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [x1]
  addClause solver [x1,x2]
  addClause solver [-x1,x2]
  ret <- solve solver
  ret @?= True

case_instantiateAtLeast :: IO ()
case_instantiateAtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addClause solver [x1]

  addAtLeast solver [x1,x2,x3,x4] 2
  ret <- solve solver
  ret @?= True

  addAtLeast solver [-x1,-x2,-x3,-x4] 2
  ret <- solve solver
  ret @?= True

case_inconsistent_AtLeast :: IO ()
case_inconsistent_AtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] 3
  ret <- solve solver -- unsat
  ret @?= False

case_trivial_AtLeast :: IO ()
case_trivial_AtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] 0
  ret <- solve solver
  ret @?= True

  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addAtLeast solver [x1,x2] (-1)
  ret <- solve solver
  ret @?= True

case_AtLeast_1 :: IO ()
case_AtLeast_1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addAtLeast solver [x1,x2,x3] 2
  addAtLeast solver [-x1,-x2,-x3] 2
  ret <- solve solver -- unsat
  ret @?= False

case_AtLeast_2 :: IO ()
case_AtLeast_2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addAtLeast solver [x1,x2,x3,x4] 2
  addClause solver [-x1,-x2]
  addClause solver [-x1,-x3]
  ret <- solve solver
  ret @?= True

case_AtLeast_3 :: IO ()
case_AtLeast_3 = do
  forM_ [(-1) .. 3] $ \n -> do
    solver <- newSolver
    x1 <- newVar solver
    x2 <- newVar solver
    addAtLeast solver [x1,x2] n
    ret <- solve solver
    assertEqual ("case_AtLeast3_" ++ show n) (n <= 2) ret

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
case_PB_sample1 :: IO ()
case_PB_sample1 = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  ret @?= True

-- 一部の変数を否定に置き換えたもの
case_PB_sample1' :: IO ()
case_PB_sample1' = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,-x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,-x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,-x4),(4,x3)] 10
  addPBExactly solver [(2,-x2),(3,-x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  ret @?= True

-- いきなり矛盾したPB制約
case_root_inconsistent_PB :: IO ()
case_root_inconsistent_PB = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(2,x1),(3,x2)] 6
  ret <- solve solver
  ret @?= False

case_pb_propagate :: IO ()
case_pb_propagate = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(1,x1),(3,x2)] 3
  addClause solver [-x1]
  ret <- solve solver
  ret @?= True

case_solveWith_1 :: IO ()
case_solveWith_1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addClause solver [x1, x2]       -- x1 or x2
  addClause solver [x1, -x2]      -- x1 or not x2
  addClause solver [-x1, -x2]     -- not x1 or not x2
  addClause solver [-x3, -x1, x2] -- not x3 or not x1 or x2

  ret <- solve solver -- sat
  ret @?= True

  ret <- solveWith solver [x3] -- unsat
  ret @?= False

  ret <- solve solver -- sat
  ret @?= True

case_solveWith_2 :: IO ()
case_solveWith_2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [-x1, x2] -- -x1 or x2
  addClause solver [x1]      -- x1

  ret <- solveWith solver [x2]
  ret @?= True

  ret <- solveWith solver [-x2]
  ret @?= False

------------------------------------------------------------------------

-- -4*(not x1) + 3*x1 + 10*(not x2)
-- = -4*(1 - x1) + 3*x1 + 10*(not x2)
-- = -4 + 4*x1 + 3*x1 + 10*(not x2)
-- = 7*x1 + 10*(not x2) - 4
case_normalizePBSum :: Assertion
case_normalizePBSum = do
  sort e @?= sort [(7,x1),(10,-x2)]
  c @?= -4
  where
    x1 = 1
    x2 = 2
    (e,c) = normalizePBSum ([(-4,-x1),(3,x1),(10,-x2)], 0)

-- -4*(not x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4 + 4*x1 + 3*x1 + 10*(not x2) >= 3
-- ⇔ 7*x1 + 10*(not x2) >= 7
-- ⇔ 7*x1 + 7*(not x2) >= 7
-- ⇔ x1 + (not x2) >= 1
case_normalizePBAtLeast :: Assertion
case_normalizePBAtLeast = (sort lhs, rhs) @?= (sort [(1,x1),(1,-x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = normalizePBAtLeast ([(-4,-x1),(3,x1),(10,-x2)], 3)

case_normalizePBExactly_1 :: Assertion
case_normalizePBExactly_1 = (sort lhs, rhs) @?= (sort [(3,x1),(2,x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = normalizePBExactly ([(6,x1),(4,x2)], 2)

case_normalizePBExactly_2 :: Assertion
case_normalizePBExactly_2 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    (lhs,rhs) = normalizePBExactly ([(2,x1),(2,x2),(2,x3)], 3)

case_cutResolve_1 :: Assertion
case_cutResolve_1 = (sort lhs, rhs) @?= (sort [(1,x3),(1,x4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = cutResolve pb1 pb2 x1

case_cutResolve_2 :: Assertion
case_cutResolve_2 = (sort lhs, rhs) @?= (sort [(3,x1),(2,-x2),(2,x4)], 3)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = cutResolve pb1 pb2 x3

case_cardinalityReduction :: Assertion
case_cardinalityReduction = (sort lhs, rhs) @?= ([1,2,3,4,5],4)
  where
    (lhs, rhs) = cardinalityReduction ([(6,1),(5,2),(4,3),(3,4),(2,5),(1,6)], 17)

case_pbSubsume_clause :: Assertion
case_pbSubsume_clause = pbSubsume ([(1,1),(1,-3)],1) ([(1,1),(1,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_1 :: Assertion
case_pbSubsume_1 = pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_2 :: Assertion
case_pbSubsume_2 = pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],3) @?= False

------------------------------------------------------------------------

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
case_hybridLearning_1 :: IO ()
case_hybridLearning_1 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11] <- replicateM 11 (newVar solver)

  addClause solver [x11, x10, x9] -- C1
  addClause solver [x8, x7, x6]   -- C2
  addClause solver [x5, x4, x3]   -- C3
  addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  replicateM 3 (varBumpActivity solver x3)
  setVarPolarity solver x3 False

  replicateM 2 (varBumpActivity solver x6)
  setVarPolarity solver x6 False

  replicateM 1 (varBumpActivity solver x9)
  setVarPolarity solver x9 False

  setVarPolarity solver x1 True

  setLearningStrategy solver LearningHybrid
  ret <- solve solver
  ret @?= True

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
-- さらに、学習したPB制約はunitにはならない。
case_hybridLearning_2 :: IO ()
case_hybridLearning_2 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12] <- replicateM 12 (newVar solver)

  addClause solver [x11, x10, x9] -- C1
  addClause solver [x8, x7, x6]   -- C2
  addClause solver [x5, x4, x3]   -- C3
  addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  addClause solver [x12, -x3]
  addClause solver [x12, -x6]
  addClause solver [x12, -x9]

  varBumpActivity solver x12
  setVarPolarity solver x12 False

  setLearningStrategy solver LearningHybrid
  ret <- solve solver
  ret @?= True

-- regression test for the bug triggered by normalized-blast-floppy1-8.ucl.opb.bz2
case_addPBAtLeast_regression :: IO ()
case_addPBAtLeast_regression = do
  solver <- newSolver
  [x1,x2,x3,x4] <- replicateM 4 (newVar solver)
  addClause solver [-x1]
  addClause solver [-x2, -x3]
  addClause solver [-x2, -x4]
  addPBAtLeast solver [(1,x1),(2,x2),(1,x3),(1,x4)] 3
  ret <- solve solver
  ret @?= False

------------------------------------------------------------------------

case_addFormula = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver

  [x1,x2,x3,x4,x5] <- replicateM 5 $ liftM Var $ newVar solver
  Tseitin.addFormula enc $ Or [Imply x1 (And [x3,x4]), Imply x2 (And [x3,x5])]
  -- x6 = x3 ∧ x4
  -- x7 = x3 ∧ x5
  Tseitin.addFormula enc $ Or [x1, x2]
  Tseitin.addFormula enc $ Imply x4 (Not x5)
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ Equiv x2 x4
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ Equiv x1 x5
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ Imply (Not x1) (And [x3,x5])
  ret <- solve solver
  ret @?= True

  Tseitin.addFormula enc $ Imply (Not x2) (And [x3,x4])
  ret <- solve solver
  ret @?= False

case_encodeConj = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- Tseitin.encodeConj enc [x1,x2]

  ret <- solveWith solver [x3]
  ret @?= True
  m <- model solver
  evalLit m x1 @?= True
  evalLit m x2 @?= True
  evalLit m x3 @?= True

  ret <- solveWith solver [-x3]
  ret @?= True
  m <- model solver
  (evalLit m x1 && evalLit m x2) @?= False
  evalLit m x3 @?= False

case_encodeDisj = do
  solver <- newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- Tseitin.encodeDisj enc [x1,x2]

  ret <- solveWith solver [x3]
  ret @?= True
  m <- model solver
  (evalLit m x1 || evalLit m x2) @?= True
  evalLit m x3 @?= True

  ret <- solveWith solver [-x3]
  ret @?= True
  m <- model solver
  evalLit m x1 @?= False
  evalLit m x2 @?= False
  evalLit m x3 @?= False

------------------------------------------------------------------------

case_MUS = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]

  ret <- solveWith solver sels
  ret @?= False

  actual <- MUS.findMUSAssumptions solver MUS.defaultOptions
  let actual'  = IS.fromList $ map (\x -> x-3) actual
      expected = map IS.fromList [[1, 2], [1, 3, 4], [1, 5, 6]]
  actual' `elem` expected @?= True

------------------------------------------------------------------------

{-
c http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
c φ= (x1) ∧ (¬x1) ∧ (¬x1∨x2) ∧ (¬x2) ∧ (¬x1∨x3) ∧ (¬x3)
c MUSes(φ) = {{C1, C2}, {C1, C3, C4}, {C1, C5, C6}}
c MCSes(φ) = {{C1}, {C2, C3, C5}, {C2, C3, C6}, {C2, C4, C5}, {C2, C4, C6}}
p cnf 3 6
1 0
-1 0
-1 2 0
-2 0
-1 3 0
-3 0
-}

case_camus_allMCSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- CAMUS.allMCSAssumptions solver sels CAMUS.defaultOptions
  let actual'   = Set.fromList $ map IS.fromList actual
      expected  = [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]
      expected' = Set.fromList $ map (IS.fromList . map (+3)) expected
  actual' @?= expected'

case_camus_allMUSAssumptions = do
  solver <- newSolver
  [x1,x2,x3] <- newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- newVars solver 6
  addClause solver [-y1, x1]
  addClause solver [-y2, -x1]
  addClause solver [-y3, -x1, x2]
  addClause solver [-y4, -x2]
  addClause solver [-y5, -x1, x3]
  addClause solver [-y6, -x3]
  actual <- CAMUS.allMUSAssumptions solver sels CAMUS.defaultOptions
  let actual'   = Set.fromList $ map IS.fromList actual
      expected  = [[1,2], [1,3,4], [1,5,6]]
      expected' = Set.fromList $ map (IS.fromList . map (+3)) expected
  actual' @?= expected'

case_camus_hittingSetDual = actual' @?= expected'
  where
    actual    = CAMUS.hittingSetDual [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]
    actual'   = Set.fromList $ map IS.fromList actual
    expected  = [[1,2], [1,3,4], [1,5,6]]
    expected' = Set.fromList $ map IS.fromList expected

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
