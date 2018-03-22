{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}

-- | Encoding of Unicode Text Segmentation rules from
-- [UAX29](http://unicode.org/reports/tr29).
module Segmentation
    ( -- * Representing segmentation rules
      Rules(..)
    , Rule(..)
    , Left(..)
    , Right(..)
    , regexp

    -- * Concrete set of rules from UAX29
    , graphemeClusterBoundaries
    ) where


import Data.Semiring(Semiring(..))
import Data.GSet

import RegExp.RegExp
import qualified RegExp.Operations as Operations

import GraphemeClusterBreak


-- | An ordered sequence of 'Rule's. Rules earlier in the list
-- have precedence over the later rules. This matters when a
-- "break here" rule follows a "don't break here" rule.
data Rules c =
    Rules [Rule c]


-- | A rule consists of a left-hand pattern, a boundary condition,
-- and a right-hand pattern. The patterns determine a position in
-- the input text, and the boundary condition either allows or
-- disallows a boundary at this location.
data Rule c
    -- | Allow break here
    = Boundary (Left c) (Right c)
    -- | Disallow break here
    | NoBoundary (Left c) (Right c)


-- | A pattern to the left of a position.
data Left c
    -- | Match from the start of text.
    = StartOfText (RegExp c)

    -- | Match from an arbitrary position.
    | AnyLeft (RegExp c)


-- | A pattern to the right of a position.
data Right c
    -- | Match to the end of text.
    = EndOfText (RegExp c)

    -- | Match to an arbitrary position.
    | AnyRight (RegExp c)


-- | Turn a list of text segmentation rules into a regular expression
-- that matches a single segment. That is, repeatedly matching prefixes
-- of the input text against the resulting regular expression will give
-- the same boundaries as the original list of rules.
regexp :: forall c. GSet c => Rules c -> RegExp c
regexp (Rules rules) =
    Operations.complement (helper rZero rules)
    where
        -- | Match any string.
        any :: RegExp c
        any =
            rStar (rLiteral one)

        left :: Left c -> RegExp c
        left (StartOfText r) =
            r
        left (AnyLeft r) =
            any `rTimes` r

        right :: Right c -> RegExp c
        right (EndOfText r) =
            r
        right (AnyRight r) =
            r `rTimes` any

        rule :: Left c -> Right c -> RegExp c
        rule l r =
            left l `rTimes` right r

        -- | Regular expression that matches strings that contain a
        -- boundary. That is, these are all the "invalid" segments
        -- since they cross a boundary. The complement of this expression
        -- gives you all valid segments.
        helper :: RegExp c -- ^ Union of all "no break" rules so far
               -> [Rule c] -- ^ Remaining rules
               -> RegExp c
        helper _ [] =
            rZero
        helper noBoundary (Boundary l r : rules) =
            rPlus
                (rule l r `Operations.difference` noBoundary)
                (helper noBoundary rules)
        helper noBoundary (NoBoundary l r : rules) =
            helper (rule l r `rPlus` noBoundary) rules



-- * Concrete set of rules from UAX29

graphemeClusterBoundaries :: Rules GraphemeClusterBreak
graphemeClusterBoundaries = Rules
    [ Boundary   (StartOfText rZero)               (AnyRight any)
    , Boundary   (AnyLeft rOne)                     (EndOfText rZero)
    , NoBoundary (AnyLeft $ lit [CR])              (AnyRight $ lit [LF])
    , Boundary   (AnyLeft $ lit [Control, CR, LF]) (AnyRight rOne)
    , Boundary   (AnyLeft rOne)                     (AnyRight $ lit [Control, CR, LF])
    , Boundary   (AnyLeft any)                     (AnyRight $ any)
    ]
    where
        lit = rLiteral

        -- | Any single character.
        any :: RegExp GraphemeClusterBreak
        any =
            lit one

