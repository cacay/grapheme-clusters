{-# LANGUAGE GADTs #-}

-- | Defines a data type of heavily normalized regular expressions
-- and function to and from the default definition.
module Simplify where


import Prelude hiding (and, or)
import qualified Data.Set as Set

import BooleanAlgebra
import RegExp (CharacterClass)


data RegExp c where
    Union CharacterClass (Set.Set (RegExp c))
    Sequence [RegExp c]


