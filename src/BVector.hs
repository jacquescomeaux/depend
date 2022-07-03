module BVector
    ( Vec (..)
    , headVec
    , headVec'
    -- , tailVec
    -- , tailVec'
    ) where

import RIO

import Data.Kind (Type)

import BNat (BNat (..), BSucc, Succ, Zero, Nat(..), IsZero (..))


type Vec :: BNat iz -> Type -> Type
data Vec n a where
    VNil :: Vec BZero a
    (:>) :: a -> Vec n a -> Vec (BSucc n) a

infixr 5 :>

deriving instance Show a => Show (Vec n a)

instance Functor (Vec n) where
    fmap _ VNil      = VNil
    fmap f (x :> xs) = f x :> fmap f xs

headVec :: Vec (BSucc n) a -> a
headVec (x :> _) = x

headVec' :: Vec (n :: BNat NZ) a -> a
headVec' (x :> _) = x

-- tailVec :: Vec (BSucc n) a -> Vec n a
-- tailVec (_ :> xs) = xs

-- tailVec' :: Vec (n :: BNat NZ) a -> _
-- tailVec' (_ :> xs) = xs

type CVec :: Nat -> Type -> Type
data CVec n a where
    CNil :: CVec Zero a
    (::>:) :: a -> CVec n a -> CVec (Succ n) a

infixr 5 ::>:

headCVec :: CVec (Succ n) a -> a
headCVec (x ::>: _) = x
headCVec CNil = error "bro"

-- tailCVec :: CVec (Succ n) a -> CVec n a
-- tailCVec (_ ::>: xs) = xs
