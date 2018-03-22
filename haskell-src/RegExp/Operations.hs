{-# LANGUAGE GADTs #-}

-- | Operations over regular expressions.
module RegExp.Operations
    ( intersection
    , complement
    , difference
    ) where


import qualified DFA
import RegExp.RegExp

import qualified Data.BooleanAlgebra as BooleanAlgebra
import Data.Semiring(Semiring(..))
import Data.GSet


-- | Regular expression that accepts words both expressions accept.
intersection :: forall c. GSet c => RegExp c -> RegExp c -> RegExp c
intersection r1 r2 =
    DFA.regexp $
        DFA.fromRegExp r1 <.> DFA.fromRegExp r2


-- | Regular expression that accepts words given expression doesn't.
complement :: GSet c => RegExp c -> RegExp c
complement r =
    DFA.regexp $
        BooleanAlgebra.complement $ DFA.fromRegExp r


-- | Regular expression that accepts words the first expression does but
-- the second doesn't.
difference :: GSet c => RegExp c -> RegExp c -> RegExp c
difference r1 r2 =
    DFA.regexp $
        DFA.fromRegExp r1 <.> BooleanAlgebra.complement (DFA.fromRegExp r2)
