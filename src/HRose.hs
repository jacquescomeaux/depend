{-|
Module      : HRose
Description : Type-level rose trees and heterogeneous tree containers

The module defines heterogeneous rose trees, which generalize
rose trees in the same manner that products generalize lists.
-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module HRose
    ( -- * Data types
      Rose (..)
    , HRose (..)
      -- * singleton-like GADTs and classes
    , SRose (..)
    , SMRose (..)
    , SMaybe (..)
      -- * emptiness
    , Empty (..)
    , IsEmpty (..)
    , testEmpty
    ) where

import RIO hiding (map)

import Data.Kind (Type, Constraint)
import GHC.Show (showSpace)
import Prelude (Show (..), showParen, showString)

import Higher (HFunctor (..), HFoldable (..), HTraversable (..), HApply (..), HApplicative (..))
import List (KnownListLen (..), SList, ListLen (..), All)
import Maybe (SMaybe (..))
import Product (Product (..))
import Singletons (Sing, pattern Sing, Known (..), SingKind (..), SomeSing (..), SingInstance (..))
import Defunct (TyCon1, type (.), type (~>), type (@@), Apply)


-- | Rose tree containing nodes of type 'a'
type Rose :: Type -> Type
data Rose a = Node a [Rose a]

-- | Singletons for 'Rose'
type SRose :: Rose k -> Type
data SRose :: Rose k -> Type where
    SNode :: Sing (a :: k) -> Sing (as :: [Rose k]) -> SRose (Node a as)

type instance Sing @(Rose k) = SRose

instance SingKind k => SingKind (Rose k) where
    type Demote (Rose k) = Rose (Demote k)
    fromSing = \case
        SNode sx sl -> Node (fromSing sx) (fromSing sl)
    toSing = \case
        (Node (toSing -> SomeSing sx) (toSing -> SomeSing sl)) ->
            SomeSing $ SNode sx sl
    singInstance = \case
        SNode Sing Sing -> SingInstance

instance (Known t, Known ts) => Known (Node t ts) where
    getSing = SNode getSing getSing

-- | Heterogeneous rose tree with holes
-- Generalizes Rose trees in the same manner that products generlize lists.
-- This definition also permits the presence of "holes" which are nodes that
-- do not contain any data.
--
-- The type is indexed by a type-level tree containing @Maybe k@, and parameterized
-- by an interpretation functor applied at each data-containing node.
type HRose :: (k -> Type) -> Rose (Maybe k) -> Type
data HRose :: (k -> Type) -> Rose (Maybe k) -> Type where
    Cons :: f t -> Product (HRose f) ts -> HRose f (Node (Just t) ts)
    -- ^ A data-containing node
    Hole :: Product (HRose f) ts -> HRose f (Node Nothing ts)
    -- ^ A node with no data

instance
    ( SingKind k
    , Known (ts :: Rose (Maybe k))
    , forall t . Known t => Show (f t)
    ) => Show (HRose f ts) where
    showsPrec a (Cons b1 b2) = case getSing @ts of
        SNode (SJust Sing) Sing -> showParen
            (a >= 11)
            (showString "Cons " . showsPrec 11 b1 . showSpace . showsPrec 11 b2)
    showsPrec a (Hole PNil) = showParen (a >= 11) (showString "Leaf")
    showsPrec a (Hole b1) = case getSing @ts of
        SNode _ Sing -> showParen (a >= 11) (showString "Hole " . showsPrec 11 b1)

instance
    ( SingKind k
    , Known (ts :: Rose (Maybe k))
    , forall t . Known t => Eq (f t)
    ) => Eq (HRose f ts) where
    (==) (Cons x xs) (Cons y ys) = case getSing @ts of
        SNode (SJust Sing) Sing -> x == y && xs == ys
    (==) (Hole xs) (Hole ys)     = case getSing @ts of
        SNode _ Sing -> xs == ys

instance HFunctor HRose where
    hmap f (Cons x xs) = Cons (f x) (hmap (hmap f) xs)
    hmap f (Hole xs)   = Hole (hmap (hmap f) xs)
    smap
        :: forall k (ts :: Rose (Maybe k)) f g .
           ( Known ts
           , SingKind k
           )
        => (forall t . Known t => f t -> g t)
        -> HRose f ts
        -> HRose g ts
    smap f h = case (h, getSing @ts) of
        (Cons x xs, SNode (SJust Sing) Sing) -> Cons (f x) (smap (smap f) xs)
        (Hole xs, SNode SNothing Sing)       -> Hole (smap (smap f) xs)

instance HFoldable HRose where
    hfoldMap f (Cons x xs) = f x <> (hfoldMap (hfoldMap f) xs)
    hfoldMap f (Hole xs)   = hfoldMap (hfoldMap f) xs
    sfoldMap
        :: forall k ts m f .
           (SingKind k, Known (ts :: Rose (Maybe k)), Monoid m)
        => (forall t . Known t => f t -> m) -> HRose f ts -> m
    sfoldMap f h = case (h, getSing @ts) of
        (Cons x xs, SNode (SJust Sing) Sing) -> f x <> (sfoldMap (sfoldMap f) xs)
        (Hole xs, SNode SNothing Sing)       -> sfoldMap (sfoldMap f) xs
    hfoldr f d (Cons x xs) = f x $ hfoldr (\hr d -> hfoldr f d hr) d xs
    hfoldr f d (Hole xs)   = hfoldr (\hr d -> hfoldr f d hr) d xs
    sfoldr
        :: forall k (ts :: Rose (Maybe k)) f b . (SingKind k, Known ts)
        => (forall t . Known t => f t -> b -> b)
        -> b
        -> HRose f ts
        -> b
    sfoldr f d (Cons x xs) = case getSing @ts of SNode (SJust Sing) Sing -> f x $ sfoldr (\hr d -> sfoldr f d hr) d xs
    sfoldr f d (Hole xs) = case getSing @ts of SNode SNothing Sing -> sfoldr (\hr d -> sfoldr f d hr) d xs

instance HTraversable HRose where
    htraverse f xs = case xs of
        Cons x xs -> Cons <$> f x <*> htraverse (htraverse f) xs
        Hole xs   -> Hole <$> htraverse (htraverse f) xs
    straverse
        :: forall k ts m f g .
           ( SingKind k
           , Known (ts :: Rose (Maybe k))
           , Applicative m
           )
        => (forall t . Known t => f t -> m (g t))
        -> HRose f ts
        -> m (HRose g ts)
    straverse f xs = case (xs, getSing @ts) of
        (Cons x xs, SNode (SJust Sing) Sing) -> Cons <$> f x <*> straverse (straverse f) xs
        (Hole xs, SNode SNothing Sing)       -> Hole <$> straverse (straverse f) xs

instance HApply HRose where
    hliftA2 f (Cons x xs) (Cons y ys) = Cons (f x y) (hliftA2 (hliftA2 f) xs ys)
    hliftA2 f (Hole xs) (Hole ys)     = Hole (hliftA2 (hliftA2 f) xs ys)
    sliftA2
        :: forall k (ts :: Rose (Maybe k)) f g h .
           ( Known ts
           , SingKind k
           )
        => (forall t . Known t => f t -> g t -> h t)
        -> HRose f ts
        -> HRose g ts
        -> HRose h ts
    sliftA2 f a b = case (a, b, getSing @ts) of
        (Cons x xs, Cons y ys, SNode (SJust Sing) Sing) -> Cons (f x y) (sliftA2 (sliftA2 f) xs ys)
        (Hole xs, Hole ys, SNode SNothing Sing)         -> Hole (sliftA2 (sliftA2 f) xs ys)

instance HApplicative HRose where
    spure
        :: forall k (ts :: Rose (Maybe k)) f .
           ( SingKind k
           , Known ts
           )
        => (forall t . Known t => f t)
        -> HRose f ts
    spure f = case getSing @ts of
        SNode (SJust Sing) Sing -> Cons f (spure (spure f))
        SNode SNothing Sing     -> Hole (spure (spure f))

--TODO need better names
-- | Structural recursion helper for rose trees with holes
type SMRose :: Rose (Maybe k) -> Type
data SMRose :: Rose (Maybe k) -> Type where
    SCons :: Product SMRose ts -> SMRose (Node (Just a) ts)
    SHole :: Product SMRose ts -> SMRose (Node Nothing ts)
class KnownMRose (t :: Rose (Maybe k)) where
    getSMRose :: SMRose t
instance (KnownListLen ts, All KnownMRose ts) => KnownMRose (Node (Just a) ts) where
    getSMRose = SCons $ cpureNP getSMRose
instance (KnownListLen ts, All KnownMRose ts) => KnownMRose (Node Nothing ts) where
    getSMRose = SHole $ cpureNP getSMRose

-- TODO make "KnownShape" class?
-- TODO this name makes no sense
cpureNP
    :: forall ts f . (KnownListLen ts, All KnownMRose ts)
    => (forall t . KnownMRose t => f t) -> Product f ts
cpureNP f = case getListLen :: ListLen ts of
    LZ -> PNil
    LS -> f ::: cpureNP f

-- | Rose trees containing only 'Nothing's
class Empty (t :: Rose (Maybe k)) where
    empty :: HRose f t
-- instance (KnownListLen ts, All Empty ts) => Empty (Node Nothing ts) where
--     empty = Hole go
--       where
--         go :: forall us f . (KnownListLen us, All Empty us) => Product (HRose f) us
--         go = case getListLen :: ListLen us of
--             LZ -> PNil
--             LS -> empty ::: go
instance Empty (Node Nothing '[]) where
    empty = Hole PNil
instance (Empty t, Empty (Node Nothing ts)) => Empty (Node Nothing (t : ts)) where
    empty = case empty :: HRose f (Node Nothing ts) of
        Hole ts -> Hole (empty ::: ts)
-- TODO the original instance might be better

-- TODO make this type work with any contraint?
-- | Helper type for returning 'Empty' constraints
data IsEmpty (t :: Rose (Maybe k)) where
    IsEmpty :: Empty t => IsEmpty t

-- | Test if a given tree shape contains only holes
testEmpty :: SMRose t -> Maybe (IsEmpty t)
testEmpty (SCons _)  = Nothing
testEmpty (SHole ts) = go <$> htraverse testEmpty ts
  where
    -- TODO make this function work with any contraint?
    -- go :: ((KnownListLen ts, All Empty ts) => r) -> Product IsEmpty ts -> r
    -- go x = \case
    --     PNil           -> x
    --     IsEmpty ::: ps -> go x ps
    go :: Product IsEmpty ts -> IsEmpty (Node Nothing ts)
    go = \case
        PNil                        -> IsEmpty
        IsEmpty ::: (go -> IsEmpty) -> IsEmpty

-- -- | Apply a constraint symbol to every element of a Rose tree
-- data AllHSym0 :: (k ~> Constraint) ~> Rose (Maybe k) ~> Constraint
-- type instance Apply AllHSym0 f = AllHSym1 f
-- data AllHSym1 :: (k ~> Constraint) -> Rose (Maybe k) ~> Constraint
-- type instance Apply (AllHSym1 f) x = AllHSym2 f x
-- type AllHSym2 f xs = AllH f xs
-- type family AllH (f :: k ~> Constraint) (ts :: Rose (Maybe k)) :: Constraint where
--     AllH f (Node Nothing  ts) = (All' (AllHSym1 f) ts)
--     AllH f (Node (Just t) ts) = (f @@ t, All' (AllHSym1 f) ts)
