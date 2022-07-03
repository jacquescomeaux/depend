module Vector
    ( Vec (..)
    , BVec (..)
    , headVec
    , tailVec
    , headBVec
    , headBVec'
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


type BVec :: B.BNat iz -> Type -> Type
data BVec n a where
    BVNil :: BVec B.BZero a
    (:>:) :: a -> BVec n a -> BVec (B.BSucc n) a

infixr 5 :>:

deriving instance Show a => Show (BVec n a)

instance Functor (BVec n) where
    fmap _ BVNil      = BVNil
    fmap f (x :>: xs) = f x :>: fmap f xs

headVec :: Vec (Succ n) a -> a
headVec (x :> _) = x

tailVec :: Vec (Succ n) a -> Vec n a
tailVec (_ :> xs) = xs

headBVec :: BVec (n :: B.BNat B.NZ) a -> a
headBVec (x :>: _) = x

headBVec' :: BVec (B.BSucc n) a -> a
headBVec' (x :>: _) = x

-- tailBVec' :: BVec (B.BSucc n) a -> BVec n a
-- tailBVec' (_ :>: xs) = xs

-- tailBVec :: BVec (n :: B.BNat B.NZ) a -> _
-- tailBVec (_ :>: xs) = xs

type CVec :: B.Nat -> Type -> Type
data CVec n a where
    CNil :: CVec B.Zero a
    (::>:) :: a -> CVec n a -> CVec (B.Succ n) a

infixr 5 ::>:

headCVec :: CVec (B.Succ n) a -> a
headCVec (x ::>: _) = x
headCVec CNil = error "bro"

-- tailCVec :: CVec (B.Succ n) a -> CVec n a
-- tailCVec (_ ::>: xs) = xs
