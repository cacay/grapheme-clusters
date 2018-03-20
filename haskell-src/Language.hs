{-# LANGUAGE MonoLocalBinds #-}

-- | The language of a regular expressions is the set of all words
-- matched by that expression. Here, we show that languages of regular
-- expressions (also called regular languages) form a Kleene algebra.
module Language
    ( Language
    , language
    ) where


import RegExp
import Operations

import Data.Semiring (Semiring(..), DetectableZero(..))
import KleeneAlgebra (KleeneAlgebra(..))
import Set (GSet(..))


-- | Regular languages, i.e. set of strings that are matched by some
-- regular expression.
newtype Language c =
    Language (RegExp c)


-- | Compute the set of all strings given regular expression matches.
language :: RegExp c -> Language c
language =
    Language


-- | Given a regular language, construct a regular expression that
-- matches precisely that language.
regexp :: Language c -> RegExp c
regexp (Language r) =
    r


-- | Equivalence of regular languages is decidable.
instance GSet c => Eq (Language c) where
    l1 == l2 =
        equivalent (regexp l1) (regexp l2)


-- | Regular languages form a semiring.
instance GSet c => Semiring (Language c) where
    zero =
        Language rZero

    one =
        Language rOne

    l1 <+> l2 =
        Language (regexp l1 `rPlus` regexp l2)

    l1 <.> l2 =
        Language (regexp l1 `rTimes` regexp l2)


-- | We can tell when a regular language is empty.
instance GSet c => DetectableZero (Language c) where
    -- | TODO: we can do this a lot more efficiently.
    isZero l =
        empty (regexp l)


-- | Regular languages form a Kleene algebra.
instance GSet c => KleeneAlgebra (Language c) where
    star l =
        Language (rStar $ regexp l)


-- TODO: regular languages form a 'GSet', but concatenation is not intersection.
-- How do we reconcile that?
