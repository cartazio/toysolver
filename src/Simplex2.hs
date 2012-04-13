module Simplex2
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Problem specification  
  , newVar
  , assertAtom
  , assertLower
  , assertUpper
  , setObj
  , setOptDir

  -- * Solving
  , check
  , optimize

  -- * Extract results
  , Model
  , model
  , getValue
  , getObjValue

  -- * Reading status
  , isFeasible
  , isOptimal

  -- * Configulation
  , setLogger
  ) where

import Prelude hiding (log)
import Control.Exception
import Control.Monad
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.HashTable.IO as H
import Text.Printf
import Data.OptDir
import System.CPUTime

import qualified LA as LA
import qualified Formula as F
import Linear

type HashTable k v = H.BasicHashTable k v

{--------------------------------------------------------------------
  The @Solver@ type
--------------------------------------------------------------------}

type Var = Int

data Solver
  = Solver
  { svTableau :: !(HashTable Var (HashTable Var Rational))
  , svLB      :: !(IORef (IM.IntMap Rational))
  , svUB      :: !(IORef (IM.IntMap Rational))
  , svModel   :: !(IORef (IM.IntMap Rational))
  , svVCnt    :: !(IORef Int)
  , svOk      :: !(IORef Bool)
  , svOptDir  :: !(IORef OptDir)

  , svLogger :: !(IORef (Maybe (String -> IO ())))
  , svNPivot  :: !(IORef Int)
  }

-- special basic variable
objVar :: Int
objVar = -1

newSolver :: IO Solver
newSolver = do
  t <- H.new
  H.insert t objVar =<< H.new
  l <- newIORef IM.empty
  u <- newIORef IM.empty
  m <- newIORef (IM.singleton objVar 0)
  v <- newIORef 0
  ok <- newIORef True
  dir <- newIORef OptMin
  logger <- newIORef Nothing
  npivot <- newIORef 0
  return $
    Solver
    { svTableau = t
    , svLB      = l
    , svUB      = u
    , svModel   = m
    , svVCnt    = v
    , svOk      = ok
    , svOptDir  = dir
    , svLogger  = logger
    , svNPivot  = npivot
    }

{--------------------------------------------------------------------
  problem description
--------------------------------------------------------------------}

newVar :: Solver -> IO Var
newVar solver = do
  v <- readIORef (svVCnt solver)
  writeIORef (svVCnt solver) $! v+1
  modifyIORef (svModel solver) (IM.insert v 0)
  return v

assertAtom :: Solver -> LA.Atom Rational -> IO ()
assertAtom solver (LA.Atom lhs op rhs) = do
  let (lhs',rhs') =
        case LA.extract LA.unitVar (lhs .-. rhs) of
          (n,e) -> (e, -n)
  (v,op,rhs') <-
    case LA.terms lhs' of
      [(1,v)] -> return (v, op, rhs')
      [(-1,v)] -> return (v, F.flipOp op, -rhs')
      _ -> do
        v <- newVar solver
        row <- newRow solver lhs'
        H.insert (svTableau solver) v row
        return (v,op,rhs')
  case op of
    F.Le  -> assertUpper solver v rhs'
    F.Ge  -> assertLower solver v rhs'
    F.Eql -> do
      assertLower solver v rhs'
      assertUpper solver v rhs'
    _ -> error "unsupported"
  return ()

assertLower :: Solver -> Var -> Rational -> IO ()
assertLower solver x l = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (Just l0', _) | l <= l0' -> return ()
    (_, Just u0') | u0' < l -> markBad solver
    _ -> do
      modifyIORef (svLB solver) (IM.insert x l)
      b <- isNonBasic solver x
      v <- getValue solver x
      when (b && not (l <= v)) $ update solver x l
      checkNBFeasibility solver

assertUpper :: Solver -> Var -> Rational -> IO ()
assertUpper solver x u = do
  l0 <- getLB solver x
  u0 <- getUB solver x
  case (l0,u0) of 
    (_, Just u0') | u0' <= u -> return ()
    (Just l0', _) | u < l0' -> markBad solver
    _ -> do
      modifyIORef (svUB solver) (IM.insert x u)
      b <- isNonBasic solver x
      v <- getValue solver x
      when (b && not (v <= u)) $ update solver x u
      checkNBFeasibility solver

-- | minimization
-- FIXME: 式に定数項が含まれる可能性を考えるとこれじゃまずい?
setObj :: Solver -> LA.Expr Rational -> IO ()
setObj solver e = do
  m <- readIORef (svModel solver)
  let v  = LA.evalExpr m e
  writeIORef (svModel solver) (IM.insert objVar v m)
  obj_row <- newRow solver e
  H.insert (svTableau solver) objVar obj_row

setOptDir :: Solver -> OptDir -> IO ()
setOptDir solver dir = writeIORef (svOptDir solver) dir

{--------------------------------------------------------------------
  Satisfiability solving
--------------------------------------------------------------------}

check :: Solver -> IO Bool
check solver = do
  let
    loop :: IO Bool
    loop = do
      -- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
      m <- selectViolatingBasicVariable solver

      case m of
        Nothing -> return True
        Just xi  -> do
          li <- getLB solver xi
          vi <- getValue solver xi
          if not (testLB li vi)
            then do
              -- select the smallest non-basic variable xj such that
              -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij > 0 && (isNothing u || v < fromJust u)) ||
                             (aij < 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    xi_def <- getDef solver xi
                    liftM (fmap snd) $ findM q xi_def
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  l <- getLB solver xi
                  pivotAndUpdate solver xi xj (fromJust l)
                  loop
            else do
              -- select the smallest non-basic variable xj such that
              -- (aij < 0 and β(xj) < uj) or (aij > 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij < 0 && (isNothing u || v < fromJust u)) ||
                             (aij > 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    xi_def <- getDef solver xi
                    liftM (fmap snd) $ findM q xi_def
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  u <- getUB solver xi
                  pivotAndUpdate solver xi xj (fromJust u)
                  loop

  ok <- readIORef (svOk solver)
  if not ok
  then return False
  else do
    log solver "check"
    result <- recordTime solver loop
    when result $ checkFeasibility solver
    return result

dualSimplex :: Solver -> IO Bool
dualSimplex solver = do
  let
    loop :: IO Bool
    loop = do
      checkOptimality solver

      -- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
      m <- selectViolatingBasicVariable solver

      case m of
        Nothing -> return True
        Just xi  -> do
          li <- getLB solver xi
          vi <- getValue solver xi
          if not (testLB li vi)
            then do
              -- select non-basic variable xj such that
              -- (aij > 0 and β(xj) < uj) or (aij < 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij > 0 && (isNothing u || v < fromJust u)) ||
                             (aij < 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    dir <- readIORef (svOptDir solver)
                    obj_def <- getDef solver objVar
                    xi_def  <- getDef solver xi
                    ws <- liftM concat $ forM xi_def $ \(aij, xj) -> do
                      b <- q (aij, xj)
                      if b
                      then do
                        cj <- getCoeff solver objVar xj
                        let ratio = if dir==OptMin then (cj / aij) else - (cj / aij)
                        return [(xj, ratio) | ratio >= 0]
                      else
                        return []
                    case ws of
                      [] -> return Nothing
                      _ -> return $ Just $ fst $ minimumBy (compare `on` snd) ws
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  l <- getLB solver xi
                  pivotAndUpdate solver xi xj (fromJust l)
                  loop
            else do
              -- select non-basic variable xj such that
              -- (aij < 0 and β(xj) < uj) or (aij > 0 and β(xj) > lj)
              let q :: (Rational, Var) -> IO Bool
                  q (aij, xj) = do
                    l <- getLB solver xj
                    u <- getUB solver xj
                    v <- getValue solver xj
                    return $ (aij < 0 && (isNothing u || v < fromJust u)) ||
                             (aij > 0 && (isNothing l || fromJust l < v))

                  find :: IO (Maybe Var)
                  find = do
                    dir <- readIORef (svOptDir solver)
                    obj_def <- getDef solver objVar
                    xi_def  <- getDef solver xi
                    ws <- liftM concat $ forM xi_def $ \(aij, xj) -> do
                      b <- q (aij, xj)
                      if b
                      then do
                        cj <- getCoeff solver objVar xj
                        let ratio = if dir==OptMin then - (cj / aij) else (cj / aij)
                        return [(xj, ratio) | ratio >= 0]
                      else
                        return []
                    case ws of
                      [] -> return Nothing
                      _ -> return $ Just $ fst $ minimumBy (compare `on` snd) ws
              r <- find
              case r of
                Nothing -> markBad solver >> return False
                Just xj -> do
                  u <- getUB solver xi
                  pivotAndUpdate solver xi xj (fromJust u)
                  loop

  ok <- readIORef (svOk solver)
  if not ok
  then return False
  else do
    log solver "dual simplex"
    result <- recordTime solver loop
    when result $ checkFeasibility solver
    return result

-- select the smallest basic variable xi such that β(xi) < li or β(xi) > ui
selectViolatingBasicVariable :: Solver -> IO (Maybe Var)
selectViolatingBasicVariable solver = do
  let
    p :: Var -> IO Bool
    p x | x == objVar = return False
    p xi = do
      li <- getLB solver xi
      ui <- getUB solver xi
      vi <- getValue solver xi
      return $ not (testLB li vi) || not (testUB ui vi)
  t <- H.toList (svTableau solver)
  findM p (sort (map fst t))

{--------------------------------------------------------------------
  Optimization
--------------------------------------------------------------------}

optimize :: Solver -> IO Bool
optimize solver = do
  ret <- check solver
  if not ret
    then return False
    else do
      log solver "optimize"
      result <- recordTime solver loop
      when result $ checkOptimality solver
      return result
  where
    loop :: IO Bool
    loop = do
      checkFeasibility solver
      ret <- selectEnteringVariable solver
      case ret of
       Nothing -> return True -- finished
       Just (c,xj) -> do
         dir <- readIORef (svOptDir solver)
         r <- if dir==OptMin
              then if c > 0
                then decreaseNB solver xj -- xj を小さくして目的関数を小さくする
                else increaseNB solver xj -- xj を大きくして目的関数を小さくする
              else if c > 0
                then increaseNB solver xj -- xj を大きくして目的関数を大きくする
                else decreaseNB solver xj -- xj を小さくして目的関数を大きくする
         if r
           then loop
           else return False -- unbounded

selectEnteringVariable :: Solver -> IO (Maybe (Rational, Var))
selectEnteringVariable solver = do
  obj_def <- getDef solver objVar
  findM canEnter (sortBy (compare `on` snd) obj_def)
  where
    canEnter :: (Rational, Var) -> IO Bool
    canEnter (_,xj) | xj == LA.unitVar = return False
    canEnter (c,xj) = do
      dir <- readIORef (svOptDir solver)
      if dir==OptMin then
        if c > 0 then canDecrease solver xj      -- xを小さくすることで目的関数を小さくできる
        else if c < 0 then canIncrease solver xj -- xを大きくすることで目的関数を小さくできる
        else return False
      else
        if c > 0 then canIncrease solver xj      -- xを大きくすることで目的関数を大きくできる
        else if c < 0 then canDecrease solver xj -- xを小さくすることで目的関数を大きくできる
        else return False

canDecrease :: Solver -> Var -> IO Bool
canDecrease solver x = do
  l <- getLB solver x
  v <- getValue solver x
  case l of
    Nothing -> return True
    Just lv -> return $! (lv < v)

canIncrease :: Solver -> Var -> IO Bool
canIncrease solver x = do
  u <- getUB solver x
  v <- getValue solver x
  case u of
    Nothing -> return True
    Just uv -> return $! (v < uv)

-- | feasibility を保ちつつ non-basic variable xj の値を大きくする
increaseNB :: Solver -> Var -> IO Bool
increaseNB solver xj = do
  col <- getCol solver xj

  -- Upper bounds of θ
  -- NOTE: xj 自体の上限も考慮するのに注意
  ubs <- liftM concat $ forM ((xj,1) : col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta >= 0) ((xi,v2), theta)
           | Just v2 <- [ui | aij > 0] ++ [li | aij < 0]
           , let theta = (v2 - v1) / aij ]

  -- β(xj) := β(xj) + θ なので θ を大きく
  case ubs of
    [] -> return False -- unbounded
    _ -> do
      let (xi, v) = fst $ minimumBy (compare `on` snd) ubs
      pivotAndUpdate solver xi xj v
      return True

-- | feasibility を保ちつつ non-basic variable xj の値を小さくする
decreaseNB :: Solver -> Var -> IO Bool
decreaseNB solver xj = do
  col <- getCol solver xj

  -- Lower bounds of θ
  -- NOTE: xj 自体の下限も考慮するのに注意
  lbs <- liftM concat $ forM ((xj,1) : col) $ \(xi,aij) -> do
    v1 <- getValue solver xi
    li <- getLB solver xi
    ui <- getUB solver xi
    return [ assert (theta <= 0) ((xi,v2), theta)
           | Just v2 <- [li | aij > 0] ++ [ui | aij < 0]
           , let theta = (v2 - v1) / aij ]

  -- β(xj) := β(xj) + θ なので θ を小さく
  case lbs of
    [] -> return False -- unbounded
    _ -> do
      let (xi, v) = fst $ maximumBy (compare `on` snd) lbs
      pivotAndUpdate solver xi xj v
      return True

-- aijがゼロの行も全部探しているのは効率が悪い
getCol :: Solver -> Var -> IO [(Var,Rational)]
getCol solver xj = do
  t <- H.toList (svTableau solver)
  liftM concat $ forM t $ \(xi, xi_def) -> do
    aijMaybe <- H.lookup xi_def xj
    case aijMaybe of
      Nothing -> return []
      Just aij -> return [(xi, aij)]

{--------------------------------------------------------------------
  Extract results
--------------------------------------------------------------------}

type Model = IM.IntMap Rational

model :: Solver -> IO Model
model solver = do
  xs <- variables solver
  liftM IM.fromList $ forM xs $ \x -> do
    val <- getValue solver x
    return (x,val)

getObjValue :: Solver -> IO Rational
getObjValue solver = getValue solver objVar  

{--------------------------------------------------------------------
  major function
--------------------------------------------------------------------}

update :: Solver -> Var -> Rational -> IO ()
update solver xj v = do
  -- log solver $ printf "before update x%d (%s)" xj (show v)
  -- dump solver

  v0 <- getValue solver xj
  let diff = v - v0

  flip H.mapM_ (svTableau solver) $ \(xi,row) -> do
    aijMaybe <- H.lookup row xj
    case aijMaybe of
      Nothing  -> return ()
      Just aij -> modifyIORef (svModel solver) $ IM.insertWith (+) xi (aij * diff)
  modifyIORef (svModel solver) $ IM.insert xj v

  -- log solver $ printf "after update x%d (%s)" xj (show v)
  -- dump solver

pivot :: Solver -> Var -> Var -> IO ()
pivot solver xr xs = do
  modifyIORef' (svNPivot solver) (+1)

  Just xr_row <- H.lookup (svTableau solver) xr
  H.delete (svTableau solver) xr

  Just ars <- H.lookup xr_row xs
  xs_def <- do
    tmp <- H.toList xr_row
    return $ (xr, 1 / ars) : [(xj, - arj / ars) | (xj,arj) <- tmp, xj /= xs]
  xs_row <- H.fromList xs_def

  flip H.mapM_ (svTableau solver) $ \(xi,xi_row) -> do
    aisMaybe <- H.lookup xi_row xs
    case aisMaybe of
      Nothing  -> return ()
      Just ais -> do
        H.delete xi_row xs
        forM_ xs_def $ \(xj,aij) -> hAdd xi_row xj (ais*aij)

  H.insert (svTableau solver) xs xs_row

pivotAndUpdate :: Solver -> Var -> Var -> Rational -> IO ()
pivotAndUpdate solver xi xj v | xi == xj = update solver xi v -- xi = xj is non-basic variable
pivotAndUpdate solver xi xj v = do
  -- xi is basic variable
  -- xj is non-basic varaible

  -- log solver $ printf "before pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

  aij <- getCoeff solver xi xj
  v0 <- getValue solver xi
  let theta = (v - v0) / aij

  flip H.mapM_ (svTableau solver) $ \(xk, xk_row) -> do
    unless (xk == xi) $ do
      akjMaybe <- H.lookup xk_row xj
      case akjMaybe of
        Nothing -> return ()
        Just akj -> modifyIORef (svModel solver) (IM.insertWith (+) xk (akj*theta))
  modifyIORef (svModel solver) (IM.insertWith (+) xj theta)
  modifyIORef (svModel solver) (IM.insert xi v)

  pivot solver xi xj

  -- log solver $ printf "after pivotAndUpdate x%d x%d (%s)" xi xj (show v)
  -- dump solver

getLB :: Solver -> Var -> IO (Maybe Rational)
getLB solver x = do
  lb <- readIORef (svLB solver)
  return $ IM.lookup x lb

getUB :: Solver -> Var -> IO (Maybe Rational)
getUB solver x = do
  ub <- readIORef (svUB solver)
  return $ IM.lookup x ub

getValue :: Solver -> Var -> IO Rational
getValue solver x = do
  m <- readIORef (svModel solver)
  return $ m IM.! x

getDef :: Solver -> Var -> IO [(Rational, Var)]
getDef solver x = do
  -- x should be basic variable or 'objVar'
  Just x_row <- H.lookup (svTableau solver) x
  xs <- H.toList x_row
  return [(aij,xj) | (xj,aij) <- xs]

getCoeff :: Solver -> Var -> Var -> IO Rational
getCoeff solver xi xj = do
  Just xi_row <- H.lookup (svTableau solver) xi
  liftM fromJust $ H.lookup xi_row xj

isBasic  :: Solver -> Var -> IO Bool
isBasic solver x =
  liftM isJust $ H.lookup (svTableau solver) x

isNonBasic  :: Solver -> Var -> IO Bool
isNonBasic solver x = liftM not (isBasic solver x)

markBad :: Solver -> IO ()
markBad solver = writeIORef (svOk solver) False

newRow :: Solver -> LA.Expr Rational -> IO (HashTable Var Rational)
newRow solver e = do
  row <- H.new
  forM_ (LA.terms e) $ \(ci,xi) -> do
    ret <- H.lookup (svTableau solver) xi
    case ret of
      Nothing -> hAdd row xi ci
      Just xi_row -> flip H.mapM_ xi_row $ \(xj,aij) -> hAdd row xj (ci*aij)
  return row

{--------------------------------------------------------------------
  utility
--------------------------------------------------------------------}

findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ [] = return Nothing
findM p (x:xs) = do
  r <- p x
  if r
  then return (Just x)
  else findM p xs

testLB :: Maybe Rational -> Rational -> Bool
testLB Nothing _  = True
testLB (Just l) x = l <= x

testUB :: Maybe Rational -> Rational -> Bool
testUB Nothing _  = True
testUB (Just u) x = x <= u

variables :: Solver -> IO [Var]
variables solver = do
  vcnt <- readIORef (svVCnt solver)
  return [0..vcnt-1]

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
  x <- readIORef ref
  writeIORef ref $! f x

recordTime :: Solver -> IO a -> IO a
recordTime solver act = do
  dumpSize solver
  writeIORef (svNPivot solver) 0

  start <- getCPUTime
  result <- act
  end <- getCPUTime

  (log solver . printf "time = %.3fs") (fromIntegral (end - start) / 10^(12::Int) :: Double)
  (log solver . printf "#pivot = %d") =<< readIORef (svNPivot solver)
  return result

hAdd :: (Num v) => HashTable Var v -> Var -> v -> IO ()
hAdd !_ !_ 0 = return ()
hAdd !h !k !v = do
  ret <- H.lookup h k
  case ret of
    Nothing -> H.insert h k v
    Just v1 ->
      case v1 + v of
        0  -> H.delete h k
        v2 -> H.insert h k v2

{--------------------------------------------------------------------
  Logging
--------------------------------------------------------------------}

-- | set callback function for receiving messages.
setLogger :: Solver -> (String -> IO ()) -> IO ()
setLogger solver logger = do
  writeIORef (svLogger solver) (Just logger)

log :: Solver -> String -> IO ()
log solver msg = logIO solver (return msg)

logIO :: Solver -> IO String -> IO ()
logIO solver action = do
  m <- readIORef (svLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger

{--------------------------------------------------------------------
  debug and tests
--------------------------------------------------------------------}

test1 :: IO ()
test1 = do
  solver <- newSolver
  setLogger solver putStrLn
  x <- newVar solver
  y <- newVar solver
  z <- newVar solver
  assertAtom solver (LA.Atom (LA.fromTerms [(7,x), (12,y), (31,z)]) F.Eql (LA.constExpr 17))
  assertAtom solver (LA.Atom (LA.fromTerms [(3,x), (5,y), (14,z)])  F.Eql (LA.constExpr 7))
  assertAtom solver (LA.Atom (LA.varExpr x) F.Ge (LA.constExpr 1))
  assertAtom solver (LA.Atom (LA.varExpr x) F.Le (LA.constExpr 40))
  assertAtom solver (LA.Atom (LA.varExpr y) F.Ge (LA.constExpr (-50)))
  assertAtom solver (LA.Atom (LA.varExpr y) F.Le (LA.constExpr 50))

  ret <- check solver
  print ret

  vx <- getValue solver x
  vy <- getValue solver y
  vz <- getValue solver z
  print $ 7*vx + 12*vy + 31*vz == 17
  print $ 3*vx + 5*vy + 14*vz == 7
  print $ vx >= 1
  print $ vx <= 40
  print $ vy >= -50
  print $ vy <= 50

test2 :: IO ()
test2 = do
  solver <- newSolver
  setLogger solver putStrLn
  x <- newVar solver
  y <- newVar solver
  assertAtom solver (LA.Atom (LA.fromTerms [(11,x), (13,y)]) F.Ge (LA.constExpr 27))
  assertAtom solver (LA.Atom (LA.fromTerms [(11,x), (13,y)]) F.Le (LA.constExpr 45))
  assertAtom solver (LA.Atom (LA.fromTerms [(7,x), (-9,y)]) F.Ge (LA.constExpr (-10)))
  assertAtom solver (LA.Atom (LA.fromTerms [(7,x), (-9,y)]) F.Le (LA.constExpr 4))

  ret <- check solver
  print ret

  vx <- getValue solver x
  vy <- getValue solver y
  let v1 = 11*vx + 13*vy
      v2 = 7*vx - 9*vy
  print $ 27 <= v1 && v1 <= 45
  print $ -10 <= v2 && v2 <= 4

{-
Minimize
 obj: - x1 - 2 x2 - 3 x3 - x4
Subject To
 c1: - x1 + x2 + x3 + 10 x4 <= 20
 c2: x1 - 3 x2 + x3 <= 30
 c3: x2 - 3.5 x4 = 0
Bounds
 0 <= x1 <= 40
 2 <= x4 <= 3
End
-}
test3 :: IO ()
test3 = do
  solver <- newSolver
  setLogger solver putStrLn
  _ <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver

  setObj solver (LA.fromTerms [(-1,x1), (-2,x2), (-3,x3), (-1,x4)])

  assertAtom solver (LA.Atom (LA.fromTerms [(-1,x1), (1,x2), (1,x3), (10,x4)]) F.Le (LA.constExpr 20))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x1), (-3,x2), (1,x3)]) F.Le (LA.constExpr 30))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x2), (-3.5,x4)]) F.Eql (LA.constExpr 0))

  assertAtom solver (LA.Atom (LA.fromTerms [(1,x1)]) F.Ge (LA.constExpr 0))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x1)]) F.Le (LA.constExpr 40))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x2)]) F.Ge (LA.constExpr 0))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x3)]) F.Ge (LA.constExpr 0))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x4)]) F.Ge (LA.constExpr 2))
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x4)]) F.Le (LA.constExpr 3))

  ret1 <- check solver
  print ret1
  dump solver

  ret2 <- optimize solver
  print ret2
  dump solver

test4 :: IO ()
test4 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  H.insert (svTableau solver) x1 =<< H.fromList [(x0, 1)]
  writeIORef (svLB solver) (IM.fromList [(x0, 0), (x1, 0)])
  writeIORef (svUB solver) (IM.fromList [(x0, 2), (x1, 3)])
  setObj solver (LA.fromTerms [(-1, x0)])

  ret <- optimize solver
  print ret
  dump solver

test5 :: IO ()
test5 = do
  solver <- newSolver
  setLogger solver putStrLn
  x0 <- newVar solver
  x1 <- newVar solver

  H.insert (svTableau solver) x1 =<< H.fromList [(x0, 1)]
  writeIORef (svLB solver) (IM.fromList [(x0, 0), (x1, 0)])
  writeIORef (svUB solver) (IM.fromList [(x0, 2), (x1, 0)])
  setObj solver (LA.fromTerms [(-1, x0)])

  checkFeasibility solver

  ret <- optimize solver
  print ret
  dump solver

{-
http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example 5.7

minimize 3 x1 + 4 x2 + 5 x3
subject to 
1 x1 + 2 x2 + 3 x3 >= 5
2 x1 + 2 x2 + 1 x3 >= 6

optimal value is 11
-}
test6 :: IO ()
test6 = do
  solver <- newSolver
  setLogger solver putStrLn
  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.Atom (LA.fromTerms [(1,x1),(2,x2),(3,x3)]) F.Ge (LA.constExpr 5))
  assertAtom solver (LA.Atom (LA.fromTerms [(2,x1),(2,x2),(1,x3)]) F.Ge (LA.constExpr 6))

  setObj solver (LA.fromTerms [(3,x1),(4,x2),(5,x3)])
  setOptDir solver OptMin
  dump solver
  checkOptimality solver
  log solver "ok"

  ret <- dualSimplex solver
  print ret
  dump solver

{-
http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example 5.7

maximize -3 x1 -4 x2 -5 x3
subject to 
-1 x1 -2 x2 -3 x3 <= -5
-2 x1 -2 x2 -1 x3 <= -6

optimal value should be -11
-}
test7 :: IO ()
test7 = do
  solver <- newSolver
  setLogger solver putStrLn
  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.Atom (LA.fromTerms [(-1,x1),(-2,x2),(-3,x3)]) F.Le (LA.constExpr (-5)))
  assertAtom solver (LA.Atom (LA.fromTerms [(-2,x1),(-2,x2),(-1,x3)]) F.Le (LA.constExpr (-6)))

  setObj solver (LA.fromTerms [(-3,x1),(-4,x2),(-5,x3)])
  setOptDir solver OptMax
  dump solver
  checkOptimality solver
  log solver "ok"

  ret <- dualSimplex solver
  print ret
  dump solver

testAssertAtom :: IO ()
testAssertAtom = do
  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.Atom (LA.constExpr 1) F.Le (LA.varExpr x0))
  ret <- getLB solver x0
  print $ ret == Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.Atom (LA.varExpr x0) F.Ge (LA.constExpr 1))
  ret <- getLB solver x0
  print $ ret == Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.Atom (LA.constExpr 1) F.Ge (LA.varExpr x0))
  ret <- getUB solver x0
  print $ ret == Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.Atom (LA.varExpr x0) F.Le (LA.constExpr 1))
  ret <- getUB solver x0
  print $ ret == Just 1

dumpSize :: Solver -> IO ()
dumpSize solver = do
  nrows <- liftM (subtract 1 . length) $ H.toList (svTableau solver)
  xs <- variables solver
  let ncols = length xs - nrows
  log solver $ printf "%d rows, %d columns" nrows ncols

dump :: Solver -> IO ()
dump solver = do
  log solver "============="

  log solver "Tableau:"
  Just obj_row <- H.lookup (svTableau solver) objVar
  obj_def <- liftM (LA.fromTerms . map (\(x,c) -> (c,x))) $ H.toList obj_row
  log solver $ printf "obj = %s" (show obj_def)

  flip H.mapM_ (svTableau solver) $ \(xi, xi_row) -> do
    when (xi /= objVar) $ do
      xi_def <- liftM (LA.fromTerms . map (\(x,c) -> (c,x))) $ H.toList xi_row
      log solver $ printf "x%d = %s" xi (show xi_def)

  log solver ""

  log solver "Assignments and Bounds:"
  objVal <- getValue solver objVar
  log solver $ printf "beta(obj) = %s" (show objVal)
  xs <- variables solver 
  forM_ xs $ \x -> do
    l <- getLB solver x
    u <- getUB solver x
    v <- getValue solver x
    log solver $ printf "beta(x%d) = %s; %s <= x%d <= %s" x (show v) (show l) x (show u)

  log solver ""
  log solver "Status:"
  is_fea <- isFeasible solver
  is_opt <- isOptimal solver
  log solver $ printf "Feasible: %s" (show is_fea)
  log solver $ printf "Optimal: %s" (show is_opt)

  log solver "============="

isFeasible :: Solver -> IO Bool
isFeasible solver = do
  xs <- variables solver
  liftM and $ forM xs $ \x -> do
    v <- getValue solver x
    l <- getLB solver x
    u <- getUB solver x
    return (testLB l v && testUB u v)

isOptimal :: Solver -> IO Bool
isOptimal solver = do
  obj <- getDef solver objVar
  ret <- selectEnteringVariable solver
  return $! isNothing ret

checkFeasibility :: Solver -> IO ()
checkFeasibility _ | True = return ()
checkFeasibility solver = do
  xs <- variables solver
  forM_ xs $ \x -> do
    v <- getValue solver x
    l <- getLB solver x
    u <- getUB solver x
    unless (testLB l v) $
      error (printf "(%s) <= x%d is violated; x%d = (%s)" (show l) x x (show v))
    unless (testUB u v) $
      error (printf "x%d <= (%s) is violated; x%d = (%s)" x (show u) x (show v))
    return ()

checkNBFeasibility :: Solver -> IO ()
checkNBFeasibility _ | True = return ()
checkNBFeasibility solver = do
  xs <- variables solver
  forM_ xs $ \x -> do
    b <- isNonBasic solver x
    when b $ do
      v <- getValue solver x
      l <- getLB solver x
      u <- getUB solver x
      unless (testLB l v) $
        error (printf "checkNBFeasibility: (%s) <= x%d is violated; x%d = (%s)" (show l) x x (show v))
      unless (testUB u v) $
        error (printf "checkNBFeasibility: x%d <= (%s) is violated; x%d = (%s)" x (show u) x (show v))

checkOptimality :: Solver -> IO ()
checkOptimality _ | True = return ()
checkOptimality solver = do
  ret <- selectEnteringVariable solver
  case ret of
    Nothing -> return () -- optimal
    Just (_,x) -> error (printf "checkOptimality: not optimal (x%d can be changed)" x)