{-|
Module      : Higher
Description : Abstractions for type-indexed containers
-}
module Higher
    ( HFunctor (..)
    , HFoldable (..)
    , HTraversable (..)
    , HApply (..)
    , HApplicative (..)
    , hfold
    , hliftA3
    , sliftA3
    , spureA
    ) where

import RIO

import Data.Functor.Compose (Compose (..))
import Data.Kind (Type)

import Singletons


type K :: Type -> Type -> Type
data K a b = K { unK :: a }

type (.) = Compose

-- TODO capture dependence between j and k
class HFunctor (h :: (j -> Type) -> k -> Type) where
    hmap :: (forall t . f t -> g t) -> h f ts -> h g ts
    smap :: (SingKind j, Known (ts :: k))
         => (forall t . Known t => f t -> g t) -> h f ts -> h g ts

class HFoldable (h :: (j -> Type) -> k -> Type) where
    --TODO include s variants
    {-# MINIMAL hfoldr | hfoldMap #-}
    hfoldr :: (forall t . f t -> b -> b) -> b -> h f ts -> b
    hfoldMap :: Monoid m => (forall t . f t -> m) -> h f ts -> m
    sfoldr :: (SingKind j, Known ts) => (forall t . Known t => f t -> b -> b) -> b -> h f ts -> b
    sfoldMap :: (SingKind j, Known ts, Monoid m) => (forall t . Known t => f t -> m) -> h f ts -> m
    -- TODO can sfoldr and sfoldMap be implemented in terms of each other?

class (HFunctor h, HFoldable h) => HTraversable (h :: (j -> Type) -> k -> Type) where
    --TODO include s variants
    {-# MINIMAL htraverse | hsequence #-}
    htraverse
        :: Applicative m
        => (forall t . f t -> m (g t))
        -> h f ts
        -> m (h g ts)
    straverse
        :: (SingKind j, Applicative m, Known (ts :: k))
        => (forall t . Known t => f t -> m (g t))
        -> h f ts
        -> m (h g ts)
    hsequence :: Applicative m => h (m . f) ts -> m (h f ts)
    -- TODO is ssequence useful?
    ssequence :: (Applicative m, Known ts) => h (m . f) ts -> m (h f ts)
    htraverse f = hsequence . hmap (Compose . f)
    hsequence = htraverse getCompose

newtype Fn f g t  = Fn { fn :: f t -> g t }
newtype Fn' f g t = Fn' { fn' :: Known t => f t -> g t }

class HFunctor a => HApply (a :: (j -> Type) -> k -> Type) where
    --TODO include s variants
    {-# MINIMAL hliftA2 | hap #-}
    hap :: a (Fn f g) ts -> a f ts -> a g ts
    sap :: Known ts => a (Fn' f g) ts -> a f ts -> a g ts
    hliftA2 :: (forall t . f t -> g t -> h t) -> a f ts -> a g ts -> a h ts
    sliftA2
        :: (SingKind j, Known (ts :: k))
        => (forall t . Known t => f t -> g t -> h t)
        -> (a f ts -> a g ts -> a h ts)
    hap = hliftA2 fn
    hliftA2 f g h = (Fn . f) `hmap` g `hap` h
-- infixl 4 <*>

class HApply h => HApplicative (h :: (j -> Type) -> (k -> Type)) where
    hpure :: (forall t . f t) -> h f ts
    spure :: (SingKind j, Known (ts :: k)) => (forall t . Known t => f t) -> h f ts

hfold :: (HFoldable h, Monoid m) => h (K m) ts -> m
hfold = hfoldMap unK

hliftA3 :: HApply h => (forall t . p t -> q t -> r t -> s t) -> h p ts -> h q ts -> h r ts -> h s ts
hliftA3 f g h i = hliftA2 (\p q -> Fn (f p q)) g h `hap` i

sliftA3
    :: (SingKind j, Known ts, HApply (h :: (j -> Type) -> k -> Type))
    => (forall t . Known t => p t -> q t -> r t -> s t)
    -> h p ts
    -> h q ts
    -> h r ts
    -> h s ts
sliftA3 f g h i = sliftA2 (\p q -> Fn' (f p q)) g h `sap` i

spureA
    :: ( SingKind j
       , Known ts
       , Applicative m
       , HApplicative h
       , HTraversable (h :: (j -> Type) -> k -> Type)
       )
    => (forall t . Known t => m (f t))
    -> m (h f ts)
spureA f = hsequence $ spure (Compose f)
