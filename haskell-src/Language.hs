{-# LANGUAGE MonoLocalBinds #-}

-- | The language of a regular expressions is the set of all words
-- matched by that expression. Here, we show that languages of regular
-- expressions (also called regular languages) form a Kleene algebra.
module Language
    ( Language
    , language
    ) where


import RegExp

import Data.Semiring (Semiring(..))
import KleeneAlgebra (KleeneAlgebra(..))
import Set (GSet(..))


-- | Regular languages, i.e. set of strings that are matches by some
-- regular expression.
newtype Language c =
    Language (RegExp c)


-- | Compute the set of all strings given regular expression matches.
language :: RegExp c -> Language c
language =
    Language


-- | Regular languages form a semiring.
instance GSet c => Semiring (Language c) where
    zero =
        Language rZero

    one =
        Language rOne

    Language r1 <+> Language r2 =
        Language (r1 `rPlus` r2)

    Language r1 <.> Language r2 =
        Language (r1 `rTimes` r2)


-- | Regular languages form a Kleene algebra.
instance GSet c => KleeneAlgebra (Language c) where
    star (Language r1) =
        Language (rStar r1)


-- TODO: regular languages form a set, but concatenation is not intersection.
-- How do we reconcile that?
