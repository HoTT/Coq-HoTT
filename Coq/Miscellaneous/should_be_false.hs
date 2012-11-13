{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

data Unit = Tt
  deriving Prelude.Show

data Bool = True
          | False
  deriving Prelude.Show

should_be_false :: Bool
should_be_false =
  eq_rect __ True __

type Is_false = ()

should_be_false_Is_false :: Is_false
should_be_false_Is_false =
  eq_rect False (unsafeCoerce Tt) should_be_false

