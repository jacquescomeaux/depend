{-# LANGUAGE UndecidableInstances #-}
module BNat
  ( Nat (..)
  , SNat (..)
  , type (+)
  , SomeNat
  , Succ
  , P
  , R
  , PS
  , PIsZero
  ) where

import RIO

import Data.Kind (Type)

import qualified GHC.TypeNats as GHC

data IsZero = Z | NZ deriving Show

type Nat :: IsZero -> Type
data Nat iz where
    Zero :: Nat Z
    X2   :: Nat NZ -> Nat NZ
    X2P1 :: Nat iz -> Nat NZ
deriving instance Show (Nat iz)

type SNat :: Nat iz -> Type
data SNat n where
    SZero :: SNat Zero
    SX2   :: SNat n -> SNat (X2 n)
    SX2P1 :: SNat n -> SNat (X2P1 n)
deriving instance Show (SNat n)

_zero :: Nat Z
_zero = Zero

_succ :: Nat iz -> Nat NZ
_succ z@Zero   = X2P1 z
_succ (X2 n)   = X2P1 n
_succ (X2P1 n) = X2 (_succ n)

type PZ :: IsZero -> IsZero -> Bool -> IsZero
type family PZ az bz c where
    PZ Z Z False = Z
    PZ az bz c   = NZ

type Carry :: Nat az -> Nat bz -> forall (c :: Bool) -> Nat (PZ az bz c)
type family Carry a b c where
    Carry Zero Zero False         = Zero
    Carry Zero Zero True          = X2P1 Zero
    Carry Zero (X2 b) False       = X2 b
    Carry Zero (X2 b) True        = X2P1 b
    Carry Zero (X2P1 b) False     = X2P1 b
    Carry Zero (X2P1 b) True      = X2 (Carry Zero b True)
    Carry (X2 a) Zero False       = X2 a
    Carry (X2 a) Zero True        = X2P1 a
    Carry (X2 a) (X2 b) False     = X2 (Carry a b False)
    Carry (X2 a) (X2 b) True      = X2P1 (Carry a b False)
    Carry (X2 a) (X2P1 b) False   = X2P1 (Carry a b False)
    Carry (X2 a) (X2P1 b) True    = X2 (Carry a b True)
    Carry (X2P1 a) Zero False     = X2P1 a
    Carry (X2P1 a) Zero True      = X2 (Carry a Zero True)
    Carry (X2P1 a) (X2 b) False   = X2P1 (Carry a b False)
    Carry (X2P1 a) (X2 b) True    = X2 (Carry a b True)
    Carry (X2P1 a) (X2P1 b) False = X2 (Carry a b True)
    Carry (X2P1 a) (X2P1 b) True  = X2P1 (Carry a b True)

type (+) :: Nat az -> Nat bz -> Nat (PZ az bz False)
type (+) a b = Carry a b False

type SomeNat :: Type
data SomeNat where
    SomeNat :: Nat iz -> SomeNat

type Succ :: Nat iz -> Nat NZ
type family Succ n where
    Succ Zero     = X2P1 Zero
    Succ (X2 n)   = X2P1 n
    Succ (X2P1 n) = X2 (Succ n)

type SuccSome :: SomeNat -> SomeNat
type family SuccSome n where
    SuccSome ('SomeNat n) = 'SomeNat (Succ n)

type PIsZero :: GHC.Nat -> IsZero
type family PIsZero n where
    PIsZero 0 = Z
    PIsZero n = NZ

type PS :: GHC.Nat -> SomeNat
type family PS n where
    PS 0 = 'SomeNat Zero
    PS n = SuccSome (PS (n GHC.- 1))

type P :: forall (n :: GHC.Nat) -> Nat (PIsZero n)
type family P (n :: GHC.Nat) :: Nat (PIsZero n) where
    P 0 = Zero
    -- P n = Succ (P (n GHC.- 1))

type R :: GHC.Nat -> Nat iz
type family R n where
    R 0 = Zero
    R n = Succ (R (n GHC.- 1))
