{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Definition of regular expressions over /character classes/
-- (i.e. sets of characters from an arbitrary type). The definition
-- is left abstract, which frees us to simplify regular expressions
-- using (sound) rewriting rules. We normalize regular expressions
-- enough to guarantee that the set of Brzozowski derivatives are
-- finite.
module RegExp
    ( CharacterClass
    , RegExp

    -- # Deconstructing regular expressions
    , RegExpView(..)
    , view
    , hide

    -- # Combining regular expressions
    , rZero
    , rOne
    , rPlus
    , rTimes
    , rStar
    , rLiteral
    ) where


import Control.Exception (assert)
import qualified Data.List
import qualified Data.Set
import Data.Set (minView)
import Data.String (IsString(..))

import Data.Semiring (Semiring(..))
import Set


-- | Sets of characters from the alphabet 'c'.
type CharacterClass c =
    Set c


-- | Regular expressions that support character classes over an alphabet
-- @c@ (so we don't have to encode them using choice). The type
-- is left abstract so we can apply rewriting rules to simplify and
-- normalize expressions. Refer to 'view' and 'RegExpView' for
-- working with 'RegExp'.
--
-- Normalizing expressions not only makes them smaller and more
-- readable, but also ensures termination for some algorithms, so
-- it is a good idea overall. We normalize with respect to the
-- following equations:
--
-- == Associativity, Commutativity, and Idempotence of @+@ (ACI)
--
-- prop> (r + s) + t = r + (s + t)
-- prop> r + s = s + t
-- prop> r + r = r
--
-- == Identity for @+@
--
-- prop> 0 + r = r
--
-- == Associativity of @.@
--
-- prop> (r . s) . t = r . (s . t)
--
-- == Identity and Annihilator for @.@
--
-- prop> 1 . r = r
-- prop> r . 1 = r
-- prop> 0 . r = 0
-- prop> r . 0 = 0
--
-- == Star
--
-- prop> (r*)* = r*
-- prop> 0* = 1
-- prop> 1* = 1
--
-- Brzozowski proved that normalizing with respect to ACI ensures
-- there are only finitely many derivatives of a regular expression.
-- So ACI is necessary for any algorithm that relies on taking repeated
-- derivatives of regular expressions.
newtype RegExp c =
    RegExp (NormalizedRegExp c)

deriving instance GSet c => Eq (RegExp c)
deriving instance (GSet c, Ord (Set c)) => Ord (RegExp c)


-- | Nicer interface for inputting regular expression over 'Char'.
instance IsString (RegExp Char) where
    fromString =
        rLiteral . fromString



-- | Standard syntax for regular expressions.
data RegExpView r c where
    -- | Match the empty string and nothing else.
    One :: RegExpView c r

    -- | Match the left or the right expression.
    Plus :: r -> r -> RegExpView c r

    -- | Match the left then the right expression.
    Times :: r -> r -> RegExpView c r

    -- | Match zero or more copies of the given expression.
    Star :: r -> RegExpView c r

    -- | Match any character in the character class. The character
    -- class might be empty, in which case this matches no strings.
    Literal :: CharacterClass c -> RegExpView c r


deriving instance Functor (RegExpView c)


-- | Expose the abstract type 'RegExp' as a 'RegExpView'.
view :: forall c. GSet c => RegExp c -> RegExpView c (RegExp c)
view (RegExp r) =
    view' r
    where
        view' :: NormalizedRegExp c -> RegExpView c (RegExp c)
        view' PZero =
            Literal zero

        view' POne =
            One

        view' (PUnion p s) =
            case s of
                (minView -> Nothing) ->
                    Literal p

                (minView -> Just (r1, minView -> Nothing)) ->
                    Plus (rLiteral p) (injectSubUnion r1)

                _ | p /= zero ->
                    Plus (rLiteral p) (RegExp $ nUnion zero s)

                (minView -> Just (r1, minView -> Just (r2, minView -> Nothing))) ->
                    Plus (injectSubUnion r1) (injectSubUnion r2)

                (minView -> Just (r1, s)) ->
                    Plus (injectSubUnion r1) (RegExp $ nUnion zero s)

                _ -> -- TODO: GHC is too dumb to see this match is complete
                    undefined

        view' (PSeq [r1, r2]) =
            Times (injectSubSeq r1) (injectSubSeq r2)
        view' (PSeq (r : l)) =
            Times (injectSubSeq r) (RegExp $ nSeq l)
        view' (PSeq []) =
            undefined

        view' (PStar r) =
            Star (injectSubStar r)


-- | Pack the public view 'RegExpView' back into the abstract view 'RegExp'.
hide :: GSet c => RegExpView c (RegExp c) -> RegExp c
hide One =
    rOne
hide (Plus r1 r2) =
    rPlus r1 r2
hide (Times r1 r2) =
    rTimes r1 r2
hide (Star r) =
    rStar r
hide (Literal p) =
    rLiteral p



-- # Normalized regular expressions

-- | A type for regular expressions normalized according to the rewriting
-- rules in 'RegExp'. This way of writing regular expressions statically
-- ensures (almost) that expressions are normalized, that is, none of the
-- rewriting rules in 'RegExp' apply. There are certain side conditions we
-- cannot check statically. These are noted for individual constructors and
-- checked using smart constructors.
--
-- The general idea is to use data types that intrinsically capture the
-- properties need. For example, instead of using binary unions, we define
-- unions over /sets/ of expressions since sets build in associativity,
-- commutativity, and idempotence. Similarly, we use lists for sequencing
-- so associativity is automatic. In addition, we put restrictions on
-- subexpressions (such as @0@ doesn't appear in a union), which further
-- regularizes the structure.
type NormalizedRegExp c =
    NZero :+: NOne :+: NUnion c :+: NSeq c :+: NStar c



-- | Normalized @0@.
data NZero =
    NZero


deriving instance Eq NZero
deriving instance Ord NZero


-- | Normalized @1@.
data NOne =
    NOne


deriving instance Eq NOne
deriving instance Ord NOne


-- | A normalized literal (character set) and/or a union of expressions. Two
-- things are happening here:
--
-- 1. We bundle character sets with unions because we want to ensure we
--    combine them using set union instead of regular expression union which
--    is syntactic.
-- 2. We define union over sets so associativity, commutativity, and
--    idempotence are automatically enforced.
--
-- We dynamically check the following condition: for any @'NUnion' p s@,
--
-- @p /= 'zero' || 'length' s >= 2@
--
-- This is to ensure that we do not have trivial unions.
--
-- Additionally, we do not allow nested unions (they can be merged into
-- the outer union), or nested zeros (they can be safely removed).
data NUnion c =
    NUnion (CharacterClass c) (Data.Set.Set (SubUnion c))


-- | Expressions that can appear under a union.
type SubUnion c =
    NOne :+: NSeq c :+: NStar c


deriving instance GSet c => Eq (NUnion c)
deriving instance (GSet c, Ord (Set c)) => Ord (NUnion c)


-- | Turn a subexpression of a union node into a regular expression.
injectSubUnion :: GSet c => SubUnion c -> RegExp c
injectSubUnion (Inl NOne) =
    RegExp $ nOne
injectSubUnion (Inr (Inl (NSeq l))) =
    RegExp $ nSeq l
injectSubUnion (Inr (Inr (NStar r))) =
    RegExp $ nStar r


-- | Normalized sequential composition of expressions. We use lists
-- to get associativity for free. Given @NSeq l@, we require (and
-- dynamically check) that @'length' l >= 2@.
--
-- Additionally, we do not allow nested zeros, ones, or sequential
-- compositions.
data NSeq c =
    NSeq [SubSeq c]


-- | Expressions that can appear under a sequence.
type SubSeq c =
    NUnion c :+: NStar c


deriving instance GSet c => Eq (NStar c)
deriving instance (GSet c, Ord (Set c)) => Ord (NStar c)


-- | Turn a subexpression of a sequencing node into a regular expression.
injectSubSeq :: GSet c => SubSeq c -> RegExp c
injectSubSeq (Inl (NUnion p s)) =
    RegExp $ nUnion p s
injectSubSeq (Inr (NStar r)) =
    RegExp $ nStar r


-- | Normalized iteration. The only difference from the usual definition
-- is we require the iterated expression to be a union or a sequential
-- composition.
data NStar c =
    NStar (SubStar c)


-- | Expressions that can appear under a star.
type SubStar c =
    NUnion c :+: NSeq c


deriving instance GSet c => Eq (NSeq c)
deriving instance (GSet c, Ord (Set c)) => Ord (NSeq c)


-- | Turn a subexpression of a star node into a regular expression.
injectSubStar :: GSet c => SubStar c -> RegExp c
injectSubStar (Inl (NUnion p s)) =
    RegExp $ nUnion p s
injectSubStar (Inr (NSeq l)) =
    RegExp $ nSeq l


-- | Smart version of 'NZero'.
nZero :: NZero :<: r => r
nZero =
    inj NZero


-- | Smart version of 'NOne'.
nOne :: NOne :<: r => r
nOne =
    inj NOne


-- | Safe and smart version of 'NUnion'.
nUnion :: (NUnion c :<: r, GSet c)
       => CharacterClass c
       -> Data.Set.Set (SubUnion c)
       -> r
nUnion p s =
    assert (p /= zero || Data.Set.size s >= 2) $
        inj (NUnion p s)


-- | Safe and smart version of 'NSeq'.
nSeq :: NSeq c :<: r => [SubSeq c] -> r
nSeq l =
    assert (length l >= 2) $
        inj (NSeq l)


-- | Smart version of 'NStar'
nStar :: NStar c :<: r => SubStar c -> r
nStar r =
    inj (NStar r)



-- # Convenient syntax for pattern matching on 'NormalizedRegExp's.

pattern PZero      <- Inl NZero
pattern POne       <- Inr (Inl NOne)
pattern PUnion p s <- Inr (Inr (Inl (NUnion p s)))
pattern PSeq l     <- Inr (Inr (Inr (Inl (NSeq l))))
pattern PStar r    <- Inr (Inr (Inr (Inr (NStar r))))

{-# COMPLETE PZero, POne, PUnion, PSeq, PStar #-}



-- # Combining regular expressions

-- | Regular expression that matches no strings.
rZero :: RegExp c
rZero =
    RegExp nZero


-- | Regular expression that matches the empty string and nothing else.
rOne :: RegExp c
rOne =
    RegExp nOne


-- | Regular expression that matches strings that either regular expression
-- matches.
rPlus :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
rPlus (RegExp r1) (RegExp r2) =
    RegExp $ rPlus' r1 r2
    where
        rPlus' :: NormalizedRegExp c -> NormalizedRegExp c -> NormalizedRegExp c
        rPlus' PZero r2 =
            r2
        
        rPlus' r1 PZero =
            r1
        
        rPlus' POne POne =
            nOne
        
        rPlus' (PUnion p1 s1) POne =
            nUnion p1 (Data.Set.insert nOne s1)
        rPlus' (PUnion p1 s1) (PUnion p2 s2) =
            nUnion (p1 <+> p2) (Data.Set.union s1 s2)
        rPlus' (PUnion p1 s1) (PSeq l) =
            nUnion p1 (Data.Set.insert (nSeq l) s1)
        rPlus' (PUnion p1 s1) (PStar r) =
            nUnion p1 (Data.Set.insert (nStar r) s1)
        
        rPlus' r1 r2@(PUnion _ _) =
            rPlus' r2 r1
        
        rPlus' (PSeq l1) POne =
            nUnion zero (Data.Set.fromList [nSeq l1, nOne :: SubUnion c])
        rPlus' r1@(PSeq _) r2@(PSeq _) | r1 == r2 =
            r1
        rPlus' r1@(PSeq l1) r2@(PSeq l2) | otherwise =
            nUnion zero (Data.Set.fromList [nSeq l1, nSeq l2 :: SubUnion c])
        rPlus' (PSeq l1) (PStar r2) =
            nUnion zero (Data.Set.fromList [nSeq l1, nStar r2 :: SubUnion c])
        
        rPlus' r1 r2@(PSeq _) =
            rPlus' r2 r1
        
        rPlus' (PStar r1) POne =
            -- Star always contains the empty string, so we could optimize
            -- this case by throwing away the @1@. We won't do so, however,
            -- since we want to stick to the interface.
            nUnion zero (Data.Set.fromList [nStar r1, nOne :: SubUnion c])
        rPlus' r1@(PStar _) r2@(PStar _) | r1 == r2 =
            r1
        rPlus' (PStar r1) (PStar r2) | otherwise  =
            nUnion zero (Data.Set.fromList [nStar r1, nStar r2 :: SubUnion c])
        rPlus' r1 r2@(PStar _) =
            rPlus' r2 r1


-- | Regular expression that matches the first expression followed
-- by the second.
rTimes :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
rTimes (RegExp r1) (RegExp r2) =
    RegExp $ rTimes' r1 r2
    where
        rTimes' :: NormalizedRegExp c -> NormalizedRegExp c -> NormalizedRegExp c
        rTimes' PZero _ =
            nZero
        rTimes' _ PZero =
            nZero
        rTimes' POne r2 =
            r2
        rTimes' r1 POne =
            r1
        rTimes' (PUnion p1 s1) (PUnion p2 s2) =
            nSeq [nUnion p1 s1, nUnion p2 s2 :: SubSeq c]
        rTimes' (PUnion p1 s1) (PSeq l2) =
            nSeq $ (nUnion p1 s1 :: SubSeq c) : l2
        rTimes' (PUnion p1 s1) (PStar r2) =
            nSeq [nUnion p1 s1, nStar r2 :: SubSeq c]
        
        rTimes' (PSeq l1) (PUnion p2 s2) =
            nSeq $ l1 ++ [nUnion p2 s2 :: SubSeq c]
        rTimes' (PSeq l1) (PSeq l2) =
            nSeq (l1 ++ l2)
        rTimes' (PSeq l1) (PStar r2) =
            nSeq $ l1 ++ [nStar r2 :: SubSeq c]
        
        rTimes' (PStar r1) (PUnion p2 s2) =
            nSeq [nStar r1, nUnion p2 s2 :: SubSeq c]
        rTimes' (PStar r1) (PSeq l2) =
            nSeq $ (nStar r1 :: SubSeq c) : l2
        rTimes' (PStar r1) (PStar r2) =
            nSeq [nStar r1, nStar r2 :: SubSeq c]


-- | Regular expression that matches zero or more copies of the given
-- expression.
rStar :: forall c. GSet c => RegExp c -> RegExp c
rStar (RegExp r) =
    RegExp $ rStar' r
    where
        rStar' :: NormalizedRegExp c -> NormalizedRegExp c
        rStar' PZero =
            nOne
        rStar' POne =
            nOne
        rStar' (PUnion p s) =
            nStar (nUnion p s :: SubStar c)
        rStar' (PSeq l) =
            nStar (nSeq l :: SubStar c)
        rStar' r@(PStar _) =
            r


-- | Regular expression that matches single character strings picked
-- from the given character class.
rLiteral :: forall c. GSet c => CharacterClass c -> RegExp c
rLiteral p | p == zero =
    RegExp nZero
rLiteral p | otherwise =
    RegExp $ nUnion p Data.Set.empty



-- # Printing

instance (GSet c, Show (CharacterClass c)) => Show (RegExp c) where
    showsPrec d (RegExp r) =
        showsPrec d r


instance (GSet c, Show (CharacterClass c)) => Show (RegExpView c (RegExp c)) where
    showsPrec d r =
        showsPrec d (hide r)


instance Show NZero where
    show NZero =
        "{}"


instance Show NOne where
    show NOne =
        "<>"


instance (GSet c, Show (CharacterClass c)) => Show (NUnion c) where
    showsPrec d (NUnion p s) =
        let
            unionPrec = 6

            literal =
                if p == zero then
                    []
                else
                    [showsPrec unionPrec p]

            elements = length literal + Data.Set.size s
        in
            showParen (d > unionPrec && elements > 1) $
                intercalate
                    (showString " + ")
                    (literal ++ map (showsPrec unionPrec) (Data.Set.toList s))


instance (GSet c, Show (CharacterClass c)) => Show (NSeq c) where
    showsPrec d (NSeq l) =
        let
            seqPrec = 7
        in
            showParen (d > seqPrec) $
                intercalate (showString "#") (map (showsPrec seqPrec) l)


instance (GSet c, Show (CharacterClass c)) => Show (NStar c) where
    showsPrec d (NStar r) =
        let
            starPrec = 8
        in
            showParen (d > starPrec) $
                showsPrec starPrec r . showString "*"


-- | Combine a list of string builders using another as a separator.
intercalate :: ShowS -> [ShowS] -> ShowS
intercalate sep l =
    foldr (.) id (Data.List.intersperse sep l)



-- # Lightweight data types à la carte

-- | Sum of two types. Essentially 'Either' with a different identity.
data f :+: g
    = Inl f
    | Inr g

infixr 6 :+:


deriving instance (Eq f, Eq g) => Eq (f :+: g)

deriving instance (Ord f, Ord g) => Ord (f :+: g)


instance (Show f, Show g) => Show (f :+: g) where
    -- | We don't display tags.
    showsPrec d (Inl f) =
        showsPrec d f
    showsPrec d (Inr g) =
        showsPrec d g


-- | Determine when a type @sub@ can be injected into a type @sup@.
class sub :<: sup where
    inj :: sub -> sup

    proj :: sup -> Maybe sub


instance f :<: f where
    inj = id

    proj = Just


instance {-# OVERLAPS #-} f :<: (f :+: g) where
    inj = Inl

    proj (Inl f) =
        Just f
    proj (Inr _) =
        Nothing


instance f :<: g => f :<: (h :+: g) where
    inj = Inr . inj

    proj (Inl _) =
        Nothing
    proj (Inr g) =
        proj g