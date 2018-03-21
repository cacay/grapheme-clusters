{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE FlexibleContexts #-}

-- | Finite state automaton represented as matrices.
module DFA
    ( DFA
    , SomeDFA(..)

    -- * Combining DFAs
    , complement
    , intersection

    -- * Convert from/to regular expressions
    , regexp
    , fromRegExp
    ) where

import Flow

import Data.Finite
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import qualified Data.Set

import Data.Semiring(Semiring(..))
import qualified BooleanAlgebra
import KleeneAlgebra
import Set

import RegExp
import Derivative
import Language (Language)
import qualified Language


import SparseVector (SparseVector)
import qualified SparseVector as Vector

import SparseMatrix (SparseMatrix)
import qualified SparseMatrix as Matrix



-- | Deterministic finite state automata with @n@ states that accept words
-- over alphabet @c@.
data DFA (n :: Nat) c =
    DFA {
        -- | The start state.
        start :: Finite n,

        -- | The transition matrix. In order to represent a deterministic
        -- machine, the following must hold:
        -- * Each row covers the entire alphabet. That is, the union of all
        --   entries on a given row must be the entire set of characters.
        -- * All entries in a row are pairwise disjoint.
        --
        -- The first requirement says that there is at least one transition
        -- from every state given a character. This requirement is easy to
        -- satisfy by adding an explicit "error" state.
        --
        -- The second requirement states that there is at most one transition
        -- given a state and a character.
        transition :: SparseMatrix n n (CharacterClass c),

        -- | Accepting states.
        accept :: SparseVector n Bool
    }


-- | A 'DFA' with an unknown number of states.
data SomeDFA c where
    SomeDFA :: KnownNat n => DFA n c -> SomeDFA c


-- | @complement d@ accepts precisely the words that @d@ doesn't.
complement :: (GSet c, KnownNat n) => DFA n c -> DFA n c
complement d =
    d {
        accept =
            accept d
                |> Vector.toList
                |> fmap not
                |> zip finites
                |> Vector.vector
    }


-- | DFA that accepts words accepted by both input DFAs.
intersection :: forall n m c. (GSet c, KnownNat n, KnownNat m)
             => DFA n c
             -> DFA m c
             -> DFA (n * m) c
intersection d1 d2 =
    withKnownNat ((sing :: SNat n) %* (sing :: SNat m)) $
    DFA {
        start =
            state (start d1) (start d2),

        transition =
            Matrix.matrix
                [ ((state n m, state n' m'), s1 <.> s2)
                | ((n, n'), s1) <- Matrix.nonZero (transition d1)
                , ((m, m'), s2) <- Matrix.nonZero (transition d2)
                ],

        accept =
            Vector.vector
                [ (state n m, a1 <.> a2)
                | (n, a1) <- Vector.nonZero (accept d1)
                , (m, a2) <- Vector.nonZero (accept d2)
                ]
    }
    where
        -- | State in the product automata that corresponds to the given
        -- pair of states.
        state :: Finite n -> Finite m -> Finite (n * m)
        state i j =
           combineProduct (i, j)


-- | Convert a DFA to a regular expression.
regexp :: forall n c. (GSet c, KnownNat n)
       => DFA n c
       -> RegExp c
regexp d =
    Language.regexp $
        (s `Matrix.times` star m `Matrix.times` t) Matrix.! (0, 0)
    where
        s :: SparseMatrix 1 n (Language c)
        s =
            Matrix.fromRows [(0, Vector.vector [(start d, injectBool True)])]

        m :: SparseMatrix n n (Language c)
        m =
            Matrix.map (Language.language . rLiteral) (transition d)

        t :: SparseMatrix n 1 (Language c)
        t =
            Matrix.transpose $
                Matrix.fromRows [(0, Vector.map injectBool (accept d))]

        injectBool :: Semiring a => Bool -> a
        injectBool True =
            one
        injectBool False =
            zero


-- | Convert a regular expression to a DFA.
fromRegExp :: forall c. (GSet c) => RegExp c -> SomeDFA c
fromRegExp r =
    case toSing (fromIntegral $ Data.Set.size derivatives) of
        SomeSing (s :: SNat n) ->
            withKnownNat s $
            let
                -- | States of the constructed DFA will be the derivatives of
                -- the input regular expression. We assign each an index.
                state :: RegExp c -> Finite n
                state r =
                    finite $ fromIntegral (Data.Set.findIndex r derivatives)


                -- | Transitions /from/ the given state.
                row :: RegExp c -> SparseVector n (CharacterClass c)
                row r =
                    Vector.vector $
                        (state rZero, BooleanAlgebra.complement $ BooleanAlgebra.ors $ next r) :
                        [ (state (derivative c r), p)
                        | p <- Data.Set.toList (next r)
                        , Just c <- [choose p]
                        ]
            in
                SomeDFA $ DFA {
                    start =
                        state r,

                    transition =
                        Matrix.fromRows
                            [(state d, row d) | d <- Data.Set.toList derivatives],

                    accept =
                        Vector.vector [(state d, nullable d) | d <- Data.Set.toList derivatives]
                }
    where
        derivatives =
            allDerivatives r