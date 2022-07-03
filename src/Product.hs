{-|
Module      : Product
Description : n-ary Products

The module defines type-indexed products.
Products generalize both lists and tuples (heterogeneous lists).
The product datatype is indexed by a type-level list of types,
and is is parameterized by an interpretation functor.
This extra level of indirection makes working with Products
more convenient, and it allows the list index to be kind-polymorphic,
meaning one can form interpretation-agnostic products of lifted datatypes.
-}
module Product
    ( Product (..)
    , (>:>)
    , indexProduct
    , prodToList
    , prod
    ) where

import RIO

import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..), (:~:)(..))

import List (type (++), LElem (..))


type K :: Type -> Type -> Type
data K a b = K { _unK :: a }

-- | N-ary product, indexed by a list of k-kinded types and
-- parameterized by an interpretation functor
type Product :: forall k . (k -> Type) -> [k] -> Type
data Product :: forall k . (k -> Type) -> [k] -> Type where
    PNil  :: Product f '[]
    -- ^ The empty 'Product'
    (:::) :: f t -> Product f ts -> Product f (t : ts)
    -- ^ Prepend a single element to a 'Product'
infixr 5 :::

-- | Product catamorphism
prod
    :: forall k (r :: (k -> Type) -> [k] -> Type) f ts .
       (forall g . r g '[])
    -> (forall g (u :: k) (us :: [k]) . g u -> r g us -> r g (u : us))
    -> Product f ts
    -> r f ts
prod d _ PNil       = d
prod d f (p ::: ps) = f p (prod d f ps)

-- | Concatenation of 'Product's
(>:>) :: Product f as -> Product f bs -> Product f (as ++ bs)
(>:>) PNil bs       = bs
(>:>) (a ::: as) bs = a ::: (as >:> bs)

-- | Select an element of a 'Product'
indexProduct :: Product f ts -> LElem ts t -> f t
indexProduct (e ::: _) LEZ      = e
indexProduct (_ ::: xs) (LES i) = indexProduct xs i
indexProduct PNil impossible    = case impossible of {}

instance TestEquality f => TestEquality (Product f) where
    testEquality PNil PNil = Just Refl
    testEquality (a ::: as) (b ::: bs) = case (testEquality a b, testEquality as bs) of
        (Just Refl, Just Refl) -> Just Refl
        _                      -> Nothing
    testEquality _ _ = Nothing

-- | Convert a homogeneous 'Product' to a list
prodToList :: Product (K a) ts -> [a]
prodToList PNil         = []
prodToList (K x ::: xs) = x : prodToList xs
