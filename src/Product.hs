{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
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
import GHC.Show (showsPrec)

import List (SList (..), type (++), LElem (..))
import Singletons (pattern Sing, Known (..), SingKind)
import Higher
    ( HFunctor (..)
    , HFoldable (..)
    , HTraversable (..)
    , HApply (..)
    , HApplicative (..)
    )


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

instance HFunctor Product where
    hmap _ PNil       = PNil
    hmap f (x ::: xs) = f x ::: hmap f xs
    smap
        :: forall k (ts :: [k]) f g .
           ( SingKind k
           , Known ts
           )
        => (forall t . Known t => f t -> g t)
        -> Product f ts
        -> Product g ts
    smap _ PNil       = PNil
    smap f (x ::: xs) = case getSing @ts of
        Sing :% Sing -> f x ::: smap f xs

instance HFoldable Product where
    hfoldMap _ PNil       = mempty
    hfoldMap f (x ::: xs) = f x <> hfoldMap f xs
    sfoldMap
        :: forall k ts m f .
           (SingKind k, Known (ts :: [k]), Monoid m)
        => (forall t . Known t => f t -> m) -> Product f ts -> m
    sfoldMap _ PNil = mempty
    sfoldMap f (x ::: xs) = case getSing @ts of
        Sing :% Sing -> f x <> sfoldMap f xs
    hfoldr :: (forall t . f t -> b -> b) -> b -> Product f ts -> b
    hfoldr _ d PNil       = d
    hfoldr f d (x ::: xs) = f x (hfoldr f d xs)
    sfoldr
        :: forall k ts f b .
           (SingKind k, Known (ts :: [k]))
        => (forall t . Known t => f t -> b -> b) -> b -> Product f ts -> b
    sfoldr _ d PNil       = d
    sfoldr f d (x ::: xs) = case getSing @ts of
        Sing :% Sing -> f x (sfoldr f d xs)

instance HTraversable Product where
    htraverse _ PNil       = pure PNil
    htraverse f (x ::: xs) = liftA2 (:::) (f x) (htraverse f xs)
    straverse
        :: forall k ts m f g .
           ( SingKind k
           , Known (ts :: [k])
           , Applicative m
           )
        => (forall t . Known t => f t -> m (g t))
        -> Product f ts
        -> m (Product g ts)
    straverse _ PNil       = pure PNil
    straverse f (x ::: xs) = case getSing @ts of
        Sing :% Sing -> liftA2 (:::) (f x) (straverse f xs)

instance HApply Product where
    hliftA2 _ PNil PNil = PNil
    hliftA2 f (x ::: xs) (y ::: ys) = f x y ::: hliftA2 f xs ys
    sliftA2
        :: forall k (ts :: [k]) f g h .
           ( SingKind k
           , Known ts
           )
        => (forall t . Known t => f t -> g t -> h t)
        -> Product f ts
        -> Product g ts
        -> Product h ts
    sliftA2 _ PNil PNil             = PNil
    sliftA2 f (x ::: xs) (y ::: ys) = case getSing @ts of
        Sing :% Sing -> f x y ::: sliftA2 f xs ys

instance HApplicative Product where
    spure
        :: forall k (ts :: [k]) f .
           ( SingKind k
           , Known ts
           )
        => (forall t . Known t => f t)
        -> Product f ts
    spure f = case getSing @ts of
        SNil         -> PNil
        Sing :% Sing -> f ::: spure f

instance (SingKind k, Known ts, forall t . Known t => Show (f t)) => Show (Product f (ts :: [k])) where
    showsPrec a xs = \x  -> "[" <> showProd xs <> x
      where
        showProd :: forall m g us . (Known us, forall u . Known u => Show (g u)) => Product g (us :: [k]) -> String
        showProd PNil         = "]"
        showProd (x ::: PNil) = case getSing @us of (Sing :% _) -> show x <> "]"
        showProd (x ::: xs)   = case getSing @us of (Sing :% Sing) -> show x <> ", " <> showProd xs

instance (SingKind k, Known ts, forall t . Known t => Eq (f t)) => Eq (Product f (ts :: [k])) where
    (==) PNil PNil = True
    (==) (x:::xs) (y:::ys) = case getSing @ts of
        Sing :% Sing -> x == y && xs == ys
