{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.BCD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Reference:
--
-- * Federico Heras, Antonio Morgado, João Marques-Silva,
--   Core-Guided binary search algorithms for maximum satisfiability,
--   Twenty-Fifth AAAI Conference on Artificial Intelligence, 2011.
--   <http://www.aaai.org/ocs/index.php/AAAI/AAAI11/paper/view/3713>
--
-- * A. Morgado, F. Heras, and J. Marques-Silva,
--   Improvements to Core-Guided binary search for MaxSAT,
--   in Theory and Applications of Satisfiability Testing (SAT 2012),
--   pp. 284-297.
--   <http://dx.doi.org/10.1007/978-3-642-31612-8_22>
--   <http://ulir.ul.ie/handle/10344/2771>
-- 
-----------------------------------------------------------------------------
module SAT.PBO.BCD
  ( Options (..)
  , defaultOptions
  , solve
  ) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified SAT as SAT
import qualified SAT.Types as SAT
import Text.Printf

data Options
  = Options
  { optLogger      :: String -> IO ()
  , optUpdateBest  :: SAT.Model -> Integer -> IO ()
  , optUpdateLB    :: Integer -> IO ()
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  }

data CoreInfo
  = CoreInfo
  { coreLits :: SAT.LitSet
  , coreLB   :: Integer
  , coreUB   :: Integer
  }

coreMidValue :: CoreInfo -> Integer
coreMidValue c
  | coreLB c + 1 == coreUB c = coreUB c -- 分岐する必要なくね?
  | otherwise = (coreLB c + coreUB c + 1) `div` 2

coreUnion :: CoreInfo -> CoreInfo -> CoreInfo
coreUnion c1 c2
  = CoreInfo
  { coreLits = IntSet.union (coreLits c1) (coreLits c2)
  , coreLB = coreLB c1 + coreLB c2
  , coreUB = coreUB c1 + coreUB c2
  }

solve :: SAT.Solver -> SAT.PBLinSum -> Options -> IO (Maybe SAT.Model)
solve solver obj opt = solveWBO solver [(c,-lit) | (c,lit) <- obj] opt

solveWBO :: SAT.Solver -> [(Integer, SAT.Lit)] -> Options -> IO (Maybe SAT.Model)
solveWBO solver weights opt = do
  -- SAT.setEnableBackwardSubsumptionRemoval solver True
  loop (IntSet.fromList [lit | (_,lit) <- weights]) Map.empty Nothing

  where
    weightsMap :: SAT.LitMap Integer
    weightsMap = IntMap.fromList [(lit,w) | (w,lit) <- weights]

    coreNew :: SAT.LitSet -> CoreInfo
    coreNew cs = CoreInfo{ coreLits = cs, coreLB = 0, coreUB = sum [weightsMap IntMap.! lit | lit <- IntSet.toList cs] + 1 }

    coreCostFun :: CoreInfo -> SAT.PBLinSum
    coreCostFun c = [(weightsMap IntMap.! lit, -lit) | lit <- IntSet.toList (coreLits c)]

    updateBest :: SAT.Model -> Maybe SAT.Model -> IO ()
    updateBest currModel lastModel =
      case lastModel of
        Nothing ->
          optUpdateBest opt currModel currVal
        Just lastModel
          | lastVal <- SAT.pbEval lastModel obj
          , currVal < lastVal ->
          optUpdateBest opt currModel currVal
        Just _ ->
          return ()
      where
        obj = [(w,-lit) | (w,lit) <- weights]
        currVal = SAT.pbEval currModel obj      

    loop :: SAT.LitSet -> Map SAT.LitSet CoreInfo -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop unrelaxed cores lastModel = do
      ss <- liftM IntMap.fromList $ forM (Map.toList cores) $ \(core,info) -> do
        sel <- SAT.newVar solver
        SAT.addPBAtMostSoft solver sel (coreCostFun info) (coreMidValue info)
        optLogger opt $ printf "BCD: %d < %s <= %d\n" (coreLB info) (show (coreCostFun info)) (coreUB info)
        optLogger opt $ printf "BCD: %d -> %s <= %d\n" sel (show (coreCostFun info)) (coreMidValue info)
        return (sel,core)
      optLogger opt $ printf "BCD: unrelaxed = %s\n" (show (IntSet.toList unrelaxed))
      ret <- SAT.solveWith solver (IntMap.keys ss ++ IntSet.toList unrelaxed)

      if ret then do
        currModel <- SAT.model solver
        updateBest currModel lastModel
        let cores' = Map.map (\info -> info{ coreUB = SAT.pbEval currModel (coreCostFun info) }) cores
        loop1 unrelaxed cores' (Just currModel)
      else do
        core <- SAT.failedAssumptions solver
        optLogger opt $ printf "BCD: core = %s\n" (show core)
        case core of
          [lit] | lit `IntMap.member` ss -> do
            let c0 = ss IntMap.! lit
                cores' = Map.update (\info -> Just (info{ coreLB = coreMidValue info })) c0 cores
            loop1 unrelaxed cores' lastModel
          _ -> do
            let coreSet     = IntSet.fromList core
                torelax     = unrelaxed `IntSet.intersection` coreSet
                unrelaxed'  = unrelaxed `IntSet.difference` coreSet
                intersected = Map.fromList [(icore, cores Map.! icore) | (lit,icore) <- IntMap.toList ss, lit `IntSet.member` coreSet]
                merged      = foldl' coreUnion (coreNew torelax) (Map.elems intersected)
                cores'      = Map.insert (coreLits merged) merged (cores `Map.difference` intersected)
            loop1 unrelaxed' cores' lastModel

    loop1 :: SAT.LitSet -> Map SAT.LitSet CoreInfo -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop1 unrelaxed cores lastModel
      | all (\info -> coreLB info + 1 >= coreUB info) (Map.elems cores) = return lastModel
      | otherwise = loop unrelaxed cores lastModel
