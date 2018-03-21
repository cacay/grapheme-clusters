{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | A generic interface for sets over a type.
module Set
    ( GSet (..)
    ) where

import Prelude hiding (and, or)
import Data.Function (on)
import qualified Data.Set
import Data.String (IsString(..))

import Data.Semiring (Semiring(..), DetectableZero(..))
import BooleanAlgebra (BooleanAlgebra(..))


-- | Sets over a type @a@.
class (BooleanAlgebra (Set a), DetectableZero (Set a), Ord (Set a)) => GSet a where
    -- | Sets of elements of @a@.
    type Set a :: *

    -- | The set containing a single element.
    singleton :: a -> Set a

    -- | Determine if an element is a member of a set.
    member :: a -> Set a -> Bool
    member a s =
        singleton a <.> s == singleton a

    -- | Return an arbitrary element from a non-empty set; and
    -- 'Nothing' if the set is empty. That is, the following properties
    -- should hold:
    --
    -- @'choose' 'zero' = 'Nothing'@
    --
    -- @s /= 'zero' ==> exists a. 'choose' s = 'Just' a && 'member' a s@
    choose :: Set a -> Maybe a



-- | Finite and cofinite subsets of a type form a 'Semiring'.
instance Ord a => Semiring (FiniteSet a) where
    zero =
        empty

    one =
        full

    (<+>) =
        union

    (<.>) =
        intersection


-- | We know when a finite or cofinite subset of a finite type is empty.
instance (Bounded a, Enum a, Ord a) => DetectableZero (FiniteSet a) where
    isZero p =
        size p == 0


-- | Finite and cofinite subsets of a type form a 'BooleanAlgebra'.
instance Ord a => BooleanAlgebra (FiniteSet a) where
    complement =
        setComplement


-- | Finite sets over the elements of a finite type.
instance (Bounded a, Enum a, Ord a) => GSet a where
    type Set a = FiniteSet a

    singleton =
        These . Data.Set.singleton

    member a (These s) =
        Data.Set.member a s
    member a (ComplementOf s) =
        Data.Set.notMember a s

    choose (These s) =
        Data.Set.lookupMin s
    choose p@(ComplementOf _) =
        if size p == 0 then
            Nothing
        else
            Just $ head [a | a <- [minBound..maxBound], member a p]



-- * Implementation of sets with a more efficient complement operation.

-- | Finite and cofinite sets over the elements of a type.
data FiniteSet a
    -- | Set containing the given elements.
    = These (Data.Set.Set a)

    -- | Set containing the complement of the given elements.
    | ComplementOf (Data.Set.Set a)


-- | Equality of finite and cofinite subsets of a finite type is decidable.
instance (Bounded a, Enum a, Ord a) => Eq (FiniteSet a) where
    These s1 == These s2 =
        s1 == s2
    p1@(These s1) == p2@(ComplementOf s2) =
         size p1 == size p2 && Data.Set.null (s1 `Data.Set.intersection` s2)
    p1@(ComplementOf _) == p2@(These _) =
        p2 == p1
    ComplementOf s1 == ComplementOf s2 =
        s1 == s2


-- | We can totally order the finite and cofinite subsets of a finite type.
instance forall a.(Bounded a, Enum a, Ord a) => Ord (FiniteSet a) where
    compare (These s1) (These s2) =
        compare s1 s2
    compare p1@(These _) p2@(ComplementOf _) =
        (compare `on` toList) p1 p2
    compare p1@(ComplementOf _) p2@(These _) =
        compare p2 p1
    compare p1@(ComplementOf _) p2@(ComplementOf _) =
        (compare `on` toList) p1 p2


-- | Nicer interface for inputting finite sets over 'Char'.
instance IsString (FiniteSet Char) where
    fromString =
        These . Data.Set.fromList


instance Show (FiniteSet Char) where
    show (These s) =
        "{" ++ Data.Set.toList s ++ "}"
    show (ComplementOf s) | Data.Set.null s =
        "."
    show (ComplementOf s) =
        "~" ++ "{" ++ Data.Set.toList s ++ "}"


-- | Set containing no elements.
empty :: FiniteSet a
empty =
    These Data.Set.empty


-- | Set containing all elements.
full :: FiniteSet a
full =
    ComplementOf Data.Set.empty


-- | Complement of a set.
setComplement :: FiniteSet a -> FiniteSet a
setComplement (These s) =
    ComplementOf s
setComplement (ComplementOf s) =
    These s


-- | Intersection of two sets.
intersection :: Ord a => FiniteSet a -> FiniteSet a -> FiniteSet a
intersection (These s1) (These s2) =
    These (Data.Set.intersection s1 s2)
intersection (These s1) (ComplementOf s2) =
    These (Data.Set.difference s1 s2)
intersection p1@(ComplementOf _) p2@(These _) =
    intersection p2 p1
intersection(ComplementOf s1) (ComplementOf s2) =
    ComplementOf (Data.Set.union s1 s2)


-- | Intersection of two sets.
union :: Ord a => FiniteSet a -> FiniteSet a -> FiniteSet a
union p1 p2 =
    complement $ (complement p1) `intersection` (complement p2)



-- * Operations on finite types

-- | Number of elements in a finite type.
sizeOfType :: forall a. (Bounded a, Enum a) => a -> Int
sizeOfType _ =
    1 + fromEnum (maxBound :: a) - fromEnum (minBound :: a)


-- | We can compute the size of finite or cofinite subsets of
-- a finite type. For infinite types, size of cofinite subsets
-- is infinite.
size :: forall a. (Bounded a, Enum a) => FiniteSet a -> Int
size (These s) =
    Data.Set.size s
size (ComplementOf s) =
    sizeOfType (undefined :: a) - Data.Set.size s


-- | We can list all elements in a finite or cofinite subset of
-- a finite type. For infinite types, size of cofinite subsets
-- is infinite, so this is not possible.
toList :: (Bounded a, Enum a, Ord a) => FiniteSet a -> [a]
toList (These s) =
    Data.Set.toList s
toList (ComplementOf s) =
    [a | a <- [minBound..maxBound], Data.Set.notMember a s]