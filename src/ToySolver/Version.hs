{-# LANGUAGE CPP #-}
module ToySolver.Version
  ( version
  , packageVersions
  ) where

import Data.List
import Data.Version
import Paths_toysolver

packageVersions :: [(String, String)]
packageVersions = sort $ tail
  [ (undefined, undefined) -- dummy
#ifdef VERSION_OptDir
  , ("OptDir",       VERSION_OptDir       )
#endif
#ifdef VERSION_array
  , ("array",        VERSION_array        )
#endif
#ifdef VERSION_base
  , ("base",         VERSION_base         )
#endif
#ifdef VERSION_bytestring
  , ("bytestring",   VERSION_bytestring   )
#endif
#ifdef VERSION_containers
  , ("containers",   VERSION_containers   )
#endif
#ifdef VERSION_data_interval
  , ("data-interval",VERSION_data_interval)
#endif
#ifdef VERSION_deepseq
  , ("deepseq",      VERSION_deepseq      )
#endif
#ifdef VERSION_filepath
  , ("filepath",     VERSION_filepath     )
#endif
#ifdef VERSION_heaps
  , ("heaps",        VERSION_heaps     )
#endif
#ifdef VERSION_mtl
  , ("mtl",          VERSION_mtl          )
#endif
#ifdef VERSION_old_locale
  , ("old_locale",   VERSION_old_locale   )
#endif
#ifdef VERSION_parse_dimacs
  , ("parse_dimacs", VERSION_parse_dimacs )
#endif
#ifdef VERSION_parsec
  , ("parsec",       VERSION_parsec       )
#endif
#ifdef VERSION_primes
  , ("primes",       VERSION_primes       )
#endif
#ifdef VERSION_queue
  , ("queue",        VERSION_queue        )
#endif
#ifdef VERSION_random
  , ("random",       VERSION_random       )
#endif
#ifdef VERSION_stm
  , ("stm",          VERSION_stm          )
#endif
#ifdef VERSION_time
  , ("time",         VERSION_time         )
#endif
#ifdef VERSION_unbounded_delays
  , ("unbounded-delays", VERSION_unbounded_delays)
#endif
#ifdef VERSION_vector_space
  , ("vector-space", VERSION_vector_space)
#endif
#ifdef VERSION_logic_TPTP
  , ("logic-TPTP",   VERSION_logic_TPTP   )
#endif
  ]
