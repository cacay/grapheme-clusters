{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleInstances #-}

-- | A very cruddy implementation of sparse matrices. I couldn't
-- find an existing implementation that had all that I needed, so
-- I cooked this up.
--
-- TODO: find a package or make nicer
module SparseMatrix
    ( SparseMatrix
    , matrix

    , plus
    , times
    , transpose

    , map
    , nonZero
    , toList
    ) where

import Flow
import Prelude hiding (map)

import Data.Function (on)
import Data.List (sortBy, groupBy, intercalate)
import Data.Ord (comparing)

import Data.Finite
import Data.Proxy
import Data.Type.Equality
import GHC.TypeNats
import Unsafe.Coerce (unsafeCoerce)

import Data.Semiring (Semiring(..), DetectableZero(..))
import KleeneAlgebra

import SparseVector (SparseVector)
import qualified SparseVector as Vector



-- | A sparse matrix with @r@ rows and @c@ columns over
-- elements of type @a@.
newtype SparseMatrix (r :: Nat) (c :: Nat) a =
    UnsafeMakeSparseMatrix {
        rows :: SparseVector r (SparseVector c a)
    }


-- | Value at the given index.
(!) :: (DetectableZero a, KnownNat r, KnownNat c)
    => SparseMatrix r c a
    -> (Finite r, Finite c)
    -> a
m ! (r, c) =
    (rows m Vector.! r) Vector.! c


-- | Construct a sparse matrix from a list of indexed elements. Indices
-- that don't appear in the list are all set to zero.
--
-- We need detectable zeros so we can filter them out.
matrix :: (DetectableZero a, KnownNat r, KnownNat c) => [((Finite r, Finite c), a)] -> SparseMatrix r c a
matrix l =
    UnsafeMakeSparseMatrix {
        rows =
            sortBy (comparing (fst . fst)) l
                |> groupBy ((==) `on` (fst . fst))
                |> fmap (\l -> (fst $ fst $ head l, fmap dropRow l))
                |> fmap (\(r, elements) -> (r, Vector.vector elements))
                |> Vector.vector
    }
    where
        dropRow :: ((r, c), a) -> (c, a)
        dropRow ((r, c), x)=
            (c, x)


-- | Matrix addition.
plus :: (DetectableZero a, KnownNat r, KnownNat c)
     => SparseMatrix r c a
     -> SparseMatrix r c a
     -> SparseMatrix r c a
plus m1 m2 =
    UnsafeMakeSparseMatrix {
        rows =
            rows m1 <+> rows m2
    }


-- | Matrix multiplication.
times :: (DetectableZero a, KnownNat r, KnownNat m, KnownNat c)
     => SparseMatrix r m a
     -> SparseMatrix m c a
     -> SparseMatrix r c a
times m1 m2 =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.map (\r -> Vector.map (\c -> r `cross` c) (rows m2Tr)) (rows m1)
    }
    where
        m2Tr =
            transpose m2

        cross v1 v2 =
            Vector.sum (v1 <+> v2)


-- | Swap the rows of a matrix with its columns.
transpose :: (DetectableZero a, KnownNat r, KnownNat c)
          => SparseMatrix r c a
          -> SparseMatrix c r a
transpose m =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.vector [(i, Vector.map (Vector.! i) (rows m)) | i <- finites]
    }


-- | We can map from matrices with one type for elements to another given
-- a semiring homomorphism. Note that this does not work for arbitrary
-- functions. Specifically, this function must map zeros to zeros.
map :: (DetectableZero a, DetectableZero b, KnownNat r, KnownNat c)
    => (a -> b)
    -> SparseMatrix r c a
    -> SparseMatrix r c b
map f m =
    UnsafeMakeSparseMatrix {
        rows =
            Vector.map (Vector.map f) (rows m)
    }


-- | Iterate over non-zero elements in a matrix.
nonZero :: (KnownNat r, KnownNat c)
        => SparseMatrix r c a
        -> [((Finite r, Finite c), a)]
nonZero m =
    concatMap
      (\(r, row) -> [((r, c), a) | (c, a) <- Vector.nonZero row])
      (Vector.nonZero $ rows m)


-- | Convert a vector to a list.
toList :: (DetectableZero a, KnownNat r, KnownNat c) => SparseMatrix r c a -> [[a]]
toList m =
    fmap Vector.toList (Vector.toList $ rows m)



-- | Square matrices form a semiring.
instance (DetectableZero a, KnownNat n) => Semiring (SparseMatrix n n a) where
    -- | Matrix where all entries are zero.
    zero =
        matrix []

    -- | Matrix where the diagonal is one.
    one =
        matrix [((i, i), one) | i <- [0..]]

    -- | Matrix addition.
    (<+>) =
        plus

    -- | Matrix multiplication.
    (<.>) =
        times


-- | We can recognize zero matrices.
instance (DetectableZero a, KnownNat n) => DetectableZero (SparseMatrix n n a) where
    isZero m =
        isZero (rows m)


-- | Square matrices over Kleene algebra form a Kleene algebra.
instance (DetectableZero a, KleeneAlgebra a, KnownNat n) => KleeneAlgebra (SparseMatrix n n a) where
    star m | Just Refl <- sameNat (Proxy @n) (Proxy @0) =
        m
    star m | Just Refl <- sameNat (Proxy @n) (Proxy @1) =
        matrix [((0,0), star (m ! (0, 0)))]
    star m =
        -- TODO: get rid of 'unsafeCoerce' or limit it to proving @n = small + large@.
        case (someNatVal (fromIntegral $ n `div` 2), someNatVal (fromIntegral $ (n + 1) `div` 2)) of
            (SomeNat (Proxy :: Proxy small), SomeNat (Proxy :: Proxy large)) ->
                UnsafeMakeSparseMatrix {
                    rows =
                        unsafeCoerce (rows top' Vector.++ rows bottom')
                }
                where
                    top :: SparseVector small (SparseVector n a)
                    bottom :: SparseVector large (SparseVector n a)
                    (top, bottom) =
                        Vector.split (unsafeCoerce $ rows m)

                    topSplit :: SparseVector small (SparseVector small a, SparseVector large a)
                    topSplit =
                        Vector.map (Vector.split . unsafeCoerce) top

                    bottomSplit :: SparseVector large (SparseVector small a, SparseVector large a)
                    bottomSplit =
                        Vector.map (Vector.split . unsafeCoerce) bottom


                    a :: SparseMatrix small small a
                    a = UnsafeMakeSparseMatrix { rows = Vector.map fst topSplit }

                    b :: SparseMatrix small large a
                    b = UnsafeMakeSparseMatrix { rows = Vector.map snd topSplit }

                    c :: SparseMatrix large small a
                    c = UnsafeMakeSparseMatrix { rows = Vector.map fst bottomSplit }

                    d :: SparseMatrix large large a
                    d = UnsafeMakeSparseMatrix { rows = Vector.map snd bottomSplit }


                    a' :: SparseMatrix small small a
                    a' = star (a `plus` (b `times` star d `times` c))

                    b' :: SparseMatrix small large a
                    b' = star (a `plus` (b `times` star d `times` c)) `times` b `times` star d

                    c' :: SparseMatrix large small a
                    c' = star (d `plus` (c `times` star a `times` b)) `times` c `times` star a

                    d' :: SparseMatrix large large a
                    d' = star (d `plus` (c `times` star a `times` b))


                    top' :: SparseMatrix small n a
                    top' =
                        UnsafeMakeSparseMatrix {
                            rows =
                                Vector.zipWith
                                    (\v1 v2 -> unsafeCoerce $ v1 Vector.++ v2)
                                    (rows a')
                                    (rows b')
                        }

                    bottom' :: SparseMatrix large n a
                    bottom' =
                        UnsafeMakeSparseMatrix {
                            rows =
                                Vector.zipWith
                                    (\v1 v2 -> unsafeCoerce $ v1 Vector.++ v2)
                                    (rows c')
                                    (rows d')
                        }
        where
            n =
                fromIntegral $ natVal (Proxy @n)



-- | Equality of matrices is decidable.
deriving instance Eq a => Eq (SparseMatrix r c a)


-- | We can totally order matrices.
deriving instance Ord a => Ord (SparseMatrix r c a)


instance (DetectableZero a, Show a, KnownNat r, KnownNat c) => Show (SparseMatrix r c a) where
    show m =
        intercalate "\n"
            [ intercalate " " (fmap (padded widest) row) | row <- grid ]

        where
            -- | Matrix as a list of lists.
            grid :: [[a]]
            grid =
                fmap Vector.toList (Vector.toList $ rows m)

            -- | Show an element of the matrix.
            show :: a -> String
            show a =
                showsPrec 11 a ""

            -- | Width of the widest entry in the matrix.
            widest :: Int
            widest =
                foldr max 0 [ length (show a) | a <- concat grid]

            -- | Show with a constant width.
            padded :: Int -> a -> String
            padded width a =
                let
                    s = show a
                in
                    s ++ take (width - length s) (repeat ' ')
