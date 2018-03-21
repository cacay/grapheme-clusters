{-# LANGUAGE GADTs #-}

-- | Operations over regular expressions.
module Operations
    ( intersection
    , complement
    ) where


import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import qualified DFA
import RegExp
import Set


-- | A regular expression that accepts words both given expressions accept
intersection :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
intersection r1 r2 =
    case (DFA.fromRegExp r1, DFA.fromRegExp r2) of
        (DFA.SomeDFA (d1 :: DFA.DFA n c), DFA.SomeDFA (d2 :: DFA.DFA m c)) ->
            withKnownNat ((sing :: SNat n) %* (sing :: SNat m)) $
            DFA.regexp $ DFA.intersection d1 d2


-- | A regular expression that accepts words the given expression doesn't.
complement :: GSet c => RegExp c -> RegExp c
complement r =
    case DFA.fromRegExp r of
        DFA.SomeDFA d ->
            DFA.regexp $ DFA.complement d