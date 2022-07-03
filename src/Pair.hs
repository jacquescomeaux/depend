{-# LANGUAGE UndecidableInstances #-}
module Pair
    ( SPair (..)
    , sFst
    , sSnd
    ) where

import RIO

import Data.Kind (Type)

import Singletons
    ( SingKind (..)
    , Known (..)
    , SingInstance (..)
    , SomeSing (..)
    , Sing
    , pattern Sing
    )


-- | Singletons for pair
type SPair :: (h, k) -> Type
data SPair ab where
    SPair :: Sing a -> Sing b -> SPair '(a, b)

type instance Sing @(h, k) = SPair

instance (SingKind h, SingKind k) => SingKind (h, k) where
    -- TODO why does this need UndecidableInstances
    type Demote (h, k) = (Demote h, Demote k)
    fromSing = \case
        SPair sa sb -> (fromSing sa, fromSing sb)
    toSing = \case
        (toSing -> SomeSing sa, toSing -> SomeSing sb) -> SomeSing $ SPair sa sb
    singInstance = \case
        SPair Sing Sing -> SingInstance

instance (Known a, Known b) => Known '(a, b) where
    getSing = SPair getSing getSing

sFst :: SPair '(a, b) -> Sing a
sFst (SPair sa _) = sa

sSnd :: SPair '(a, b) -> Sing b
sSnd (SPair _ sb) = sb
