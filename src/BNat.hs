{-# LANGUAGE UndecidableInstances #-}
module BNat
    ( BNat (BZero)
    , BSucc
    , Nat
    , Succ
    , Zero
    , SNat (SZ)
    , SS
    , showNat
    , P
    , KnownNat (..)
    , snatToNat
    , IsZero (..)
    ) where

import RIO

import Data.Kind (Type, Constraint)

import qualified GHC.TypeNats as GHC

data IsZero = Z | NZ

type Zeroness :: Nat -> IsZero
type family Zeroness n where
    Zeroness (N (_ :: BNat iz)) = iz

type BNat :: IsZero -> Type
data BNat iz where
    BZero :: BNat Z
    X2    :: BNat NZ -> BNat NZ
    X2P1  :: BNat iz -> BNat NZ

type BSucc :: BNat iz -> BNat NZ
type family BSucc n = r | r -> n where
    BSucc BZero    = X2P1 BZero
    BSucc (X2 n)   = X2P1 n
    BSucc (X2P1 n) = X2 (BSucc n)

type Nat :: Type
data Nat where
    N :: BNat iz -> Nat

type Zero :: Nat
type Zero = N BZero

type Succ :: Nat -> Nat
type family Succ n = r | r -> n where
    Succ (N n) = N (BSucc n)

type SNat :: Nat -> Type
data SNat n where
    SZ    :: SNat (N BZero)
    SX2   :: SNat (N n) -> SNat (N (X2 n))
    SX2P1 :: SNat (N n) -> SNat (N (X2P1 n))

type KnownNat :: Nat -> Constraint
class KnownNat n where
    getSNat :: SNat n

instance KnownNat (N BZero) where
    getSNat = SZ

instance KnownNat (N n) => KnownNat (N (X2 n)) where
    getSNat = SX2 getSNat

instance KnownNat (N n) => KnownNat (N (X2P1 n)) where
    getSNat = SX2P1 getSNat

type SS :: SNat n -> SNat (Succ n)
type family SS n where
    SS SZ        = SX2P1 SZ
    SS (SX2 n)   = SX2P1 n
    SS (SX2P1 n) = SX2 (SS n)

type P :: GHC.Nat -> Nat
type family P n where
    P 0 = Zero
    P n = Succ (P (n GHC.- 1))

type GZeroness :: GHC.Nat -> IsZero
type family GZeroness n where
    GZeroness 0 = Z
    GZeroness n = NZ

type B :: forall (n :: GHC.Nat) -> BNat (GZeroness n)
type family B (n :: GHC.Nat) :: BNat (GZeroness n) where
    B 0 = BZero
    -- B n = Succ (B (n GHC.- 1))

type R :: GHC.Nat -> BNat iz
type family R n where
    R 0 = BZero
    R n = BSucc (R (n GHC.- 1))

showNat :: Nat -> Text
showNat (N BZero) = "0"
showNat (N n) = showNat' n
  where
    showNat' :: BNat iz -> Text
    showNat' BZero    = mempty
    showNat' (X2 m)   = showNat' m <> "0"
    showNat' (X2P1 m) = showNat' m <> "1"

snatToNat :: SNat n -> Nat
snatToNat n = N (snatToNat' n)
  where
    snatToNat' :: SNat n -> BNat (Zeroness n)
    snatToNat' SZ         = BZero
    snatToNat' (SX2 sn)   = X2 (snatToNat' sn)
    snatToNat' (SX2P1 sn) = X2P1 (snatToNat' sn)

type PZ :: IsZero -> IsZero -> Bool -> IsZero
type family PZ az bz c where
    PZ Z Z False = Z
    PZ az bz c   = NZ
    
type BCarry :: BNat az -> BNat bz -> forall (c :: Bool) -> BNat (PZ az bz c)
type family BCarry a b c where
    BCarry BZero BZero False       = BZero
    BCarry BZero BZero True        = X2P1 BZero
    BCarry BZero (X2 b) False      = X2 b
    BCarry BZero (X2 b) True       = X2P1 b
    BCarry BZero (X2P1 b) False    = X2P1 b
    BCarry BZero (X2P1 b) True     = X2 (BCarry BZero b True)
    BCarry (X2 a) BZero False      = X2 a
    BCarry (X2 a) BZero True       = X2P1 a
    BCarry (X2 a) (X2 b) False     = X2 (BCarry a b False)
    BCarry (X2 a) (X2 b) True      = X2P1 (BCarry a b False)
    BCarry (X2 a) (X2P1 b) False   = X2P1 (BCarry a b False)
    BCarry (X2 a) (X2P1 b) True    = X2 (BCarry a b True)
    BCarry (X2P1 a) BZero False    = X2P1 a
    BCarry (X2P1 a) BZero True     = X2 (BCarry a BZero True)
    BCarry (X2P1 a) (X2 b) False   = X2P1 (BCarry a b False)
    BCarry (X2P1 a) (X2 b) True    = X2 (BCarry a b True)
    BCarry (X2P1 a) (X2P1 b) False = X2 (BCarry a b True)
    BCarry (X2P1 a) (X2P1 b) True  = X2P1 (BCarry a b True)

type Carry :: Nat -> Nat -> Bool -> Nat
type family Carry a b c where
    Carry (N a) (N b) c = N (BCarry a b c)

type (+) :: Nat -> Nat -> Nat
type (+) a b = Carry a b False
  
