{-# LANGUAGE UndecidableInstances #-}
module Triple
    ( STriple (..)
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


-- | Singletons for triple (3-tuple)
type STriple :: (i, j, k) -> Type
data STriple abc where
    STriple :: Sing a -> Sing b -> Sing c -> STriple '(a, b, c)

type instance Sing @(i, j, k) = STriple

instance (SingKind i, SingKind j, SingKind k) => SingKind (i, j, k) where
    -- needs undecidable instances
    type Demote (i, j, k) = (Demote i, Demote j, Demote k)
    fromSing = \case
        STriple sa sb sc -> (fromSing sa, fromSing sb, fromSing sc)
    toSing = \case
        ( toSing -> SomeSing sa
         ,toSing -> SomeSing sb
         ,toSing -> SomeSing sc
         )-> SomeSing $ STriple sa sb sc
    singInstance = \case
        STriple Sing Sing Sing -> SingInstance

instance (Known a, Known b, Known c) => Known '(a, b, c) where
    getSing = STriple getSing getSing getSing
