{-# LANGUAGE GADTs #-}

-- | Derivatives of regular expressions that support character classes.
-- The development follows
-- [Symbolic Solving of Extended Regular Expression Inequalities](https://arxiv.org/abs/1410.3227).
module Derivative
    (
    -- * Tests
      nullable
    , empty
    , equivalent

    -- * Derivatives
    , derivative
    , partialDerivative

    -- * Automata construction
    , allDerivatives
    , next
    ) where

import qualified Data.Set

import RegExp

import BooleanAlgebra hiding (complement)
import Data.Semiring (Semiring(..))
import Set


-- * Tests

-- | 'True' if and only if the regular expression can match the
-- empty string.
nullable :: GSet c => RegExp c -> Bool
nullable r =
    case view r of
        One ->
            True

        Plus r1 r2 ->
            nullable r1 || nullable r2

        Times r1 r2 ->
            nullable r1 && nullable r2

        Star _ ->
            True

        Literal _ ->
            False


-- | 'True' if and only if the regular expression matches no strings.
empty :: GSet c => RegExp c -> Bool
empty r =
    case view r of
        One ->
            False

        Plus r1 r2 ->
            empty r1 && empty r2

        Times r1 r2 ->
            empty r1 || empty r2

        Star _ ->
            False

        Literal p ->
            p == zero


-- | Two regular expressions are equivalent if only if they match
-- the same set of strings.
equivalent :: forall c. GSet c => RegExp c -> RegExp c -> Bool
equivalent =
    helper Data.Set.empty
    where
        -- TODO: do we have to use union find instead? It will certainly be more
        -- efficient, but we might in fact need it for completeness.
        helper :: Data.Set.Set (RegExp c, RegExp c) -> RegExp c -> RegExp c -> Bool
        helper context r1 r2 | (r1, r2) `Data.Set.member` context =
            True
        helper _ r1 r2 | nullable r1 /= nullable r2 =
            False
        helper context r1 r2 =
            let
                derivatives =
                    [ (derivative c r1, derivative c r2)
                    | p <- Data.Set.toList (next r1 `join` next r2)
                    , Just c <- [choose p]
                    ]
            in
                all (uncurry $ helper $ Data.Set.insert (r1, r2) context) derivatives



-- * Operations

-- | Brzozowski derivative of a regular expression with respect to a character.
-- @derivative c r@ matches a word @w@ if and only if @r@ matches @cw@.
derivative :: GSet c => c -> RegExp c -> RegExp c
derivative c r =
    case view r of
        One ->
            rZero

        Plus r1 r2 ->
            rPlus (derivative c r1) (derivative c r2)

        Times r1 r2 | nullable r1 ->
            rPlus (derivative c r1 `rTimes` r2) (derivative c r2)

        Times r1 r2 | otherwise ->
            derivative c r1 `rTimes` r2

        Star r' ->
            derivative c r' `rTimes` r

        Literal p ->
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



-- * Automaton construction


-- | Set of derivatives of a regular expression under all words.
allDerivatives :: forall c. GSet c => RegExp c -> Data.Set.Set (RegExp c)
allDerivatives r =
    Data.Set.insert rZero (helper Data.Set.empty [r])
    where
        helper :: Data.Set.Set (RegExp c) -> [RegExp c] -> Data.Set.Set (RegExp c)
        helper context [] =
            context

        helper context (r : rest) | r `Data.Set.member` context =
            helper context rest

        helper context (r : rest) =
            let
                derivatives =
                    [ derivative c r | p <- Data.Set.toList (next r)
                                     , Just c <- [choose p]]
            in
                helper (Data.Set.insert r context) (derivatives ++ rest)


-- * Helpers

-- | Given a regular expression @r@, compute equivalence classes of
-- character classes such that:
--
-- * @p `member` next r@ and @c1 `member` p && c2 `member` p@ implies
--   @derivative c1 r = derivative c2 r@,
-- * @not $ c `member` ors (next r)@ implies @derivative c r ~ rZero@.
next :: GSet c => RegExp c -> Data.Set.Set (CharacterClass c)
next r =
    case view r of
        One ->
            Data.Set.singleton zero

        Plus r1 r2 ->
            join (next r1) (next r2)

        Times r1 r2 | nullable r1 ->
            join (next r1) (next r2)

        Times r1 _ | otherwise ->
            next r1

        Star r ->
            next r

        Literal p  ->
            Data.Set.singleton p


-- | Given two sets of mutually disjoint character classes, compute
-- a set of mutually disjoint character classes that cover both input
-- sets. More concretely, given @s1@ and @s2@ such that
--
-- @'disjoint' s1 && 'disjoint' s2@
--
-- we have:
--
-- * @'ors' ('join' s1 s2) = 'ors' s1 <+> 'ors' s2@
-- * @'disjoint' ('join' s1 s2)@
-- * @'all' (\p -> 'all' (\p1 -> p '<.>' p1 == 'zero' || p `subset` p1) s1) ('join' s1 s2)@
-- * @'all' (\p -> 'all' (\p2 -> p '<.>' p2 == 'zero' || p `subset` p2) s2) ('join' s1 s2)@
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