{-# LANGUAGE UndecidableInstances #-}
module Nat
    ( Nat (..)
    , SNat (..)
    , KnownNat (..)
    , P
    ) where

import RIO

import Data.Kind (Type, Constraint)

import qualified GHC.TypeNats as GHC


type Nat :: Type
data Nat = Zero | Succ Nat deriving Show

type SNat :: Nat -> Type
data SNat n where
    SZ :: SNat Zero
    SS :: SNat n -> SNat (Succ n)

deriving instance Show (SNat n)

type (+) :: Nat -> Nat -> Nat
type family (+) a b where
    (+) Zero b = b
    (+) (Succ a) b = Succ (a + b)

type KnownNat :: Nat -> Constraint
class KnownNat n where
    getSNat :: SNat n

instance KnownNat Zero where
    getSNat = SZ

instance KnownNat n => KnownNat (Succ n) where
    getSNat = SS getSNat

-- needs UndecidableInstances
type P :: GHC.Nat -> Nat
type family P n where
    P 0 = Zero
    P n = Succ (P (n GHC.- 1))
