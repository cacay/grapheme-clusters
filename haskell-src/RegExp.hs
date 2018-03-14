{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Intersection and complement of regular expressions. The development
-- follows
-- [Symbolic Solving of Extended Regular Expression Inequalities](https://arxiv.org/abs/1410.3227).
module RegExp
    ( RegExp (..)
    , CharacterClass
    , zero

    -- # Tests
    , nullable
    , empty

    -- # Operations
    , derivative
    , partialDerivative
    , intersection
    , complement
    ) where

import qualified Data.Set
import Data.String (IsString(..))

import BooleanAlgebra hiding (complement)
import Data.Semiring (Semiring(..))
import Set


-- | A set of characters from the alphabet 'c'.
type CharacterClass c =
    Set c


-- | Regular expressions over an alphabet @c@. One difference
-- from conventional regular expressions is that we work with
-- character classes explicitly instead of encoding them using
-- 'Plus'.
--
-- Note that @0@ can be represented using @Literal false@
-- so it is excluded.
data RegExp c where
    -- | Match the empty string and nothing else
    One :: RegExp c

    -- | Match the left or the right expression
    Plus :: RegExp c -> RegExp c -> RegExp c

    -- | Match the left then the right expression
    Times :: RegExp c -> RegExp c -> RegExp c

    -- | Match zero or more copies of the expression
    Star :: RegExp c -> RegExp c

    -- | Match any character in the character class
    Literal :: CharacterClass c -> RegExp c


-- | The regular expression that matches no strings.
rZero :: GSet c => RegExp c
rZero =
    Literal zero


instance Show (CharacterClass c) => Show (RegExp c) where
    show One =
        "<>"
    show (Plus r1 r2) =
        "(" ++ show r1 ++ " + " ++ show r2 ++ ")"
    show (Times r1 r2) =
        "(" ++ show r1 ++ ", " ++ show r2 ++ ")"
    show (Star r) =
        "(" ++ show r ++ ")" ++ "*"
    show (Literal p) =
        show p


-- | Nicer interface for inputting regular expression over 'Char'.
instance IsString (RegExp Char) where
    fromString = Literal . fromString


deriving instance GSet c => Eq (RegExp c)

deriving instance GSet c => Ord (RegExp c)



-- # Tests

-- | 'True' if and only if the regular expression can match the
-- empty string.
nullable :: RegExp c -> Bool
nullable One =
    True
nullable (Plus r1 r2) =
    nullable r1 || nullable r2
nullable (Times r1 r2) =
    nullable r1 && nullable r2
nullable (Star _) =
    True
nullable (Literal _) =
    False


-- | 'True' if and only if the regular expression matches no strings.
empty :: GSet c => RegExp c -> Bool
empty One =
    False
empty (Plus r1 r2) =
    empty r1 && empty r2
empty (Times r1 r2) =
    empty r1 || empty r2
empty (Star _) =
    False
empty (Literal s) =
    s == zero


-- # Operations

-- | Brzozowski derivative of a regular expression with respect to a character.
-- @derivative c r@ matches a word @w@ if and only if @r@ matches @cw@.
derivative :: GSet c => c -> RegExp c -> RegExp c
derivative c One =
    rZero
derivative c (Plus r1 r2) =
    Plus (derivative c r1) (derivative c r2)
derivative c (Times r1 r2) | nullable r1 =
    Plus (derivative c r1 `Times` r2) (derivative c r2)
derivative c (Times r1 r2) | otherwise =
    derivative c r1 `Times` r2
derivative c e@(Star r) =
    derivative c r `Times` e
derivative c (Literal p) =
    if c `member` p then One else rZero


-- | Antimirov derivative of a regular expression with respect to a character.
-- This is similar to 'derivative', but returns a set of regular expressions
-- whose union is equivalent to the Brzozowski derivative.
partialDerivative :: forall c. GSet c
                  => c
                  -> RegExp c
                  -> Data.Set.Set (RegExp c)
partialDerivative c r =
    case r of
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
            if c `member` p then Data.Set.singleton One else Data.Set.empty

    where
        setTimes :: Data.Set.Set (RegExp c) -> RegExp c -> Data.Set.Set (RegExp c)
        setTimes s r =
            Data.Set.map (`Times` r) s


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
next One =
    Data.Set.singleton zero
next (Plus r1 r2) =
    join (next r1) (next r2)
next (Times r1 r2) | nullable r1 =
    join (next r1) (next r2)
next (Times r1 _) | otherwise =
    next r1
next (Star r) =
    next r
next (Literal p) =
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
