{-# LANGUAGE GADTs #-}

-- | Operations over regular expressions.
module RegExp.Operations
    ( intersection
    , complement
    , difference
    ) where


import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import qualified DFA
import RegExp.RegExp

import Data.GSet


-- | Regular expression that accepts words both expressions accept.
intersection :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
intersection r1 r2 =
    case (DFA.fromRegExp r1, DFA.fromRegExp r2) of
        (DFA.SomeDFA (d1 :: DFA.DFA n c), DFA.SomeDFA (d2 :: DFA.DFA m c)) ->
            withKnownNat ((sing :: SNat n) %* (sing :: SNat m)) $
            DFA.regexp $ DFA.intersection d1 d2


-- | Regular expression that accepts words given expression doesn't.
complement :: GSet c => RegExp c -> RegExp c
complement r =
    case DFA.fromRegExp r of
        DFA.SomeDFA d ->
            DFA.regexp $ DFA.complement d


-- | Regular expression that accepts words the first expression does but
-- the second doesn't.
difference :: GSet c => RegExp c -> RegExp c -> RegExp c
difference r1 r2 =
    -- TODO: implement directly
    r1 `intersection` complement r2