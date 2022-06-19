module BNat
  ( Nat (..)
  , SNat (..)
  ) where

import Prelude (Show, Bool (..))

import Data.Kind (Type)

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

zero :: Nat Z
zero = Zero

succ :: Nat iz -> Nat NZ
succ z@Zero   = X2P1 z
succ (X2 n)   = X2P1 n
succ (X2P1 n) = X2 (succ n)

type SBool :: Bool -> Type
data SBool b where
    STrue  :: SBool True
    SFalse :: SBool False

type PZ :: IsZero -> IsZero -> Bool -> IsZero
type family PZ az bz c where
    PZ Z Z False = Z
    PZ az bz c   = NZ

type Carry :: Nat az -> Nat bz -> SBool c -> Nat (PZ az bz c)
type family Carry a b c where
  Carry Zero Zero SFalse         = Zero
  Carry Zero Zero STrue          = X2P1 Zero
  Carry Zero (X2 b) SFalse       = X2 b
  Carry Zero (X2 b) STrue        = X2P1 b
  Carry Zero (X2P1 b) SFalse     = X2P1 b
  Carry Zero (X2P1 b) STrue      = X2 (Carry Zero b STrue)
  Carry (X2 a) Zero SFalse       = X2 a
  Carry (X2 a) Zero STrue        = X2P1 a
  Carry (X2 a) (X2 b) SFalse     = X2 (Carry a b SFalse)
  Carry (X2 a) (X2 b) STrue      = X2P1 (Carry a b SFalse)
  Carry (X2 a) (X2P1 b) SFalse   = X2P1 (Carry a b SFalse)
  Carry (X2 a) (X2P1 b) STrue    = X2 (Carry a b STrue)
  Carry (X2P1 a) Zero SFalse     = X2P1 a
  Carry (X2P1 a) Zero STrue      = X2 (Carry a Zero STrue)
  Carry (X2P1 a) (X2 b) SFalse   = X2P1 (Carry a b SFalse)
  Carry (X2P1 a) (X2 b) STrue    = X2 (Carry a b STrue)
  Carry (X2P1 a) (X2P1 b) SFalse = X2 (Carry a b STrue)
  Carry (X2P1 a) (X2P1 b) STrue  = X2P1 (Carry a b STrue)

type (+) :: Nat az -> Nat bz -> Nat (PZ az bz False)
type (+) a b = Carry a b SFalse
