{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}


module InfiniteBooleanAlgebra where

import Prelude hiding (and, or)
import qualified Data.Set as Set

import BooleanAlgebra (BooleanAlgebra(..))


-- | Types that have infinitely many elements. This is witnessed by
-- embedding 'Integer' into the type. This embedding should be injective,
-- but of course Haskell can't check that; the user needs to ensure correctness.
class Infinite a where
    -- | An injective function from the smallest infinite set into 'a'
    infinite :: Integer -> a


-- | Boolean algebra of finite and co-finite subsets of an /infinite/ alphabet.
-- This instance is incorrect for finite types (equality doesn't work).
instance (Infinite c, Ord c) => BooleanAlgebra c where
    data Predicate c
        -- | Predicate that holds for the elements in the set
        = These (Set.Set c)

        -- | Predicate that holds for the elements in the complement of the set
        | ComplementOf (Set.Set c)
        deriving (Eq, Ord)

    true =
        ComplementOf (Set.empty)

    false =
        These (Set.empty)

    complement (These s) =
        ComplementOf s
    complement (ComplementOf s) =
        These s

    and (These s1) (These s2) =
        These (Set.intersection s1 s2)
    and (These s1) (ComplementOf s2) =
        These (Set.difference s1 s2)
    and p1@(ComplementOf _) p2@(These _) =
        and p2 p1
    and (ComplementOf s1) (ComplementOf s2) =
        ComplementOf (Set.union s1 s2)

    or p1 p2 =
        complement $ (complement p1) `and` (complement p2)

    singleton c =
        These (Set.singleton c)

    holds c (These s) =
        Set.member c s
    holds c (ComplementOf s) =
        Set.notMember c s

    choose (These s) =
        Set.lookupMin s
    choose p@(ComplementOf _) =
        Just $ head [c | x <- [0..], let c = infinite x, not (holds c p)]
