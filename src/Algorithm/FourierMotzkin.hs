{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.FourierMotzkin
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Fourier-Motzkin Variable Elimination
-- 
-- Reference:
--
-- * <http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf>
--
-----------------------------------------------------------------------------
module Algorithm.FourierMotzkin
    ( Lit (..)
    , project
    , projectN
    , eliminateQuantifiers
    , solveFormula
    , solve
    ) where

import Algorithm.FourierMotzkin.Core
import Algorithm.FourierMotzkin.FOL
