module Nat
    ( Nat
    ) where

import Data.Kind (Type)


type Nat :: Type
data Nat = Zero | Succ Nat

type SNat :: Nat -> Type
data SNat n where
    SZ :: SNat Zero
    SS :: SNat n -> SNat (Succ n)

