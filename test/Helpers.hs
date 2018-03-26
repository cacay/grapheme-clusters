{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


-- | Helper functions for testing.
module Helpers where

import GHC.Generics

import Test.SmallCheck.Series


-- | A finite data type with a few constructors. Useful with SmallCheck.
data Small
    = A
    | B
    | C
    deriving (Eq, Ord, Bounded, Enum, Show, Generic)


instance Monad m => Serial m Small