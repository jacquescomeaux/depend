module Maybe
    ( SMaybe (..)
    , MMaybe
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
import Defunct (Apply, type (@@), type (~>))


-- | Singletons for 'Maybe'
type SMaybe :: Maybe k -> Type
data SMaybe mx where
    SNothing :: SMaybe Nothing
    SJust    :: Sing t -> SMaybe (Just t)

type instance Sing @(Maybe k) = SMaybe

instance SingKind k => SingKind (Maybe k) where
    type Demote (Maybe k) = Maybe (Demote k)
    fromSing = \case
        SNothing  -> Nothing
        SJust sx  -> Just (fromSing sx)
    toSing = \case
        Nothing   -> SomeSing SNothing
        Just (toSing -> SomeSing sx) -> SomeSing $ SJust sx
    singInstance = \case
        SNothing   -> SingInstance
        SJust Sing -> SingInstance

instance Known Nothing where
    getSing = SNothing
instance Known t => Known (Just t) where
    getSing = SJust getSing

-- | Type-level 'maybe' catamorphism
-- I'd like to call this 'Maybe', but there's an obvious naming conflict
type family MMaybe (d :: b) (f :: a ~> b) (mx :: Maybe a) :: b where
    MMaybe d f Nothing  = d
    MMaybe d f (Just x) = f @@ x

-- | Defunctionalization symbols for 'MMaybe'
data MMaybeSym0 :: b ~> (a ~> b) ~> Maybe a ~> b
type instance Apply MMaybeSym0 d = MMaybeSym1 d
data MMaybeSym1 :: b -> (a ~> b) ~> Maybe a ~> b
type instance Apply (MMaybeSym1 d) f = MMaybeSym2 d f
data MMaybeSym2 :: b -> (a ~> b) -> Maybe a ~> b
type instance Apply (MMaybeSym2 d f) mx = MMaybeSym3 d f mx
type MMaybeSym3 d f mx = MMaybe d f mx
