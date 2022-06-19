module Vector
    ( Vec (..)
    , BVec (..)
    ) where

import RIO

import Nat (Nat (..))

import Data.Kind (Type)

import qualified BNat as B


type Vec :: Nat -> Type -> Type
data Vec n a where
    VNil :: Vec Zero a
    (:>) :: a -> Vec n a -> Vec (Succ n) a

infixr 5 :>

deriving instance Show a => Show (Vec n a)


type BVec :: B.Nat iz -> Type -> Type
data BVec n a where
    BVNil :: BVec B.Zero a
    (:>:) :: a -> BVec n a -> BVec (B.Succ n) a

infixr 5 :>:

deriving instance Show a => Show (BVec n a)
