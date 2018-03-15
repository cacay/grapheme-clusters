{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Intersection and complement of regular expressions. The development
-- follows
-- [Symbolic Solving of Extended Regular Expression Inequalities](https://arxiv.org/abs/1410.3227).
module Operations
    (
    -- # Tests
      nullable
    , empty

    -- # Operations
    , derivative
    , partialDerivative
    , intersection
    , complement
    ) where

import qualified Data.Set

import RegExp

import BooleanAlgebra hiding (complement)
import Data.Semiring (Semiring(..))
import Set


-- # Tests

-- | 'True' if and only if the regular expression can match the
-- empty string.
nullable :: GSet c => RegExp c -> Bool
nullable (view -> One) =
    True
nullable (view -> Plus r1 r2) =
    nullable r1 || nullable r2
nullable (view -> Times r1 r2) =
    nullable r1 && nullable r2
nullable (view -> Star _) =
    True
nullable (view -> Literal _) =
    False


-- | 'True' if and only if the regular expression matches no strings.
empty :: GSet c => RegExp c -> Bool
empty (view -> One) =
    False
empty (view -> Plus r1 r2) =
    empty r1 && empty r2
empty (view -> Times r1 r2) =
    empty r1 || empty r2
empty (view -> Star _) =
    False
empty (view -> Literal s) =
    s == zero


-- # Operations

-- | Brzozowski derivative of a regular expression with respect to a character.
-- @derivative c r@ matches a word @w@ if and only if @r@ matches @cw@.
derivative :: GSet c => c -> RegExp c -> RegExp c
derivative c (view -> One) =
    rZero
derivative c (view -> Plus r1 r2) =
    rPlus (derivative c r1) (derivative c r2)
derivative c (view -> Times r1 r2) | nullable r1 =
    rPlus (derivative c r1 `rTimes` r2) (derivative c r2)
derivative c (view -> Times r1 r2) | otherwise =
    derivative c r1 `rTimes` r2
derivative c e@(view -> Star r) =
    derivative c r `rTimes` e
derivative c (view -> Literal p) =
    if c `member` p then rOne else rZero


-- | Antimirov derivative of a regular expression with respect to a character.
-- This is similar to 'derivative', but returns a set of regular expressions
-- whose union is equivalent to the Brzozowski derivative.
partialDerivative :: forall c. GSet c
                  => c
                  -> RegExp c
                  -> Data.Set.Set (RegExp c)
partialDerivative c r =
    case view r of
        One ->
            Data.Set.empty

        Plus r1 r2 ->
            partialDerivative c r1 `Data.Set.union` partialDerivative c r2

        Times r1 r2 | nullable r1 ->
            Data.Set.union
                (partialDerivative c r1 `setTimes` r2)
                (partialDerivative c r2)

        Times r1 r2 | otherwise ->
            partialDerivative c r1 `setTimes` r2

        Star r' ->
            partialDerivative c r' `setTimes` r

        Literal p ->
            if c `member` p then Data.Set.singleton rOne else Data.Set.empty

    where
        setTimes :: Data.Set.Set (RegExp c) -> RegExp c -> Data.Set.Set (RegExp c)
        setTimes s r =
            Data.Set.map (`rTimes` r) s


intersection :: GSet c => RegExp c -> RegExp c -> RegExp c
intersection =
    undefined


complement :: GSet c => RegExp c -> RegExp c
complement =
    undefined



-- # Helpers

-- | Given a regular expression @r@, compute equivalence classes of
-- character classes such that:
--
-- * @p `member` next r@ and @c1 `member` p && c2 `member` p@ implies
--   @derivative c1 r = derivative c2 r@,
-- * @not $ c `member` ors (next r)@ implies @derivative c r ~ rZero@.
next :: GSet c => RegExp c -> Data.Set.Set (CharacterClass c)
next (view -> One) =
    Data.Set.singleton zero
next (view -> Plus r1 r2) =
    join (next r1) (next r2)
next (view -> Times r1 r2) | nullable r1 =
    join (next r1) (next r2)
next (view -> Times r1 _) | otherwise =
    next r1
next (view -> Star r) =
    next r
next (view -> Literal p) =
    Data.Set.singleton p


-- | Given two sets of mutually disjoint character classes, compute
-- a set of mutually disjoint character classes that cover both input
-- sets. More concretely, given @s1@ and @s2@ such that
--
-- prop> disjoint s1 && disjoint s2
--
-- we have:
--
-- prop> ors (join s1 s2) = ors s1 <+> ors s2
-- prop> disjoint (join s1 s2)
-- prop> all (\p -> all (\p1 -> p <.> p1 == zero || p `subset` p1) s1) (join s1 s2)
-- prop> all (\p -> all (\p2 -> p <.> p2 == zero || p `subset` p2) s2) (join s1 s2)
join :: GSet c
     => Data.Set.Set (CharacterClass c)
     -> Data.Set.Set (CharacterClass c)
     -> Data.Set.Set (CharacterClass c)
join s1 s2 = Data.Set.fromList $ concat $ do
    p1 <- Data.Set.toList s1
    p2 <- Data.Set.toList s2
    return
        [ p1 <.> p2
        , p1 `butNot` ors s2
        , p2 `butNot` ors s1
        ]


-- | Test if a set of character classes are pairwise disjoint.
disjoint :: GSet c => Data.Set.Set (CharacterClass c) -> Bool
disjoint s =
    let s' = Data.Set.toList s in
        and [ p1 <.> p2 == zero | p1 <- s', p2 <- s', p1 /= p2 ]
