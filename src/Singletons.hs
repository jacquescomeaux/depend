module Singletons
    ( Sing
    , SomeSing (..)
    , SingKind (..)
    , Known (..)
    , SingInstance (..)
    , withSingI
    , withSing
    , withSomeSing
    , pattern Sing
    , pattern FromSing
    , Sigma (..)
    ) where

import Data.Kind (Type)


-- | The Sing type family, for dependent universal quantification
type family Sing :: k -> Type

-- | Existential wrapper for reified terms
data SomeSing :: Type -> Type where
    SomeSing :: Sing (a :: k) -> SomeSing k

-- | Reification and reflection between terms and singletons
class SingKind k where
    type Demote k = (r :: Type) | r -> k
    fromSing :: Sing (a :: k) -> Demote k
    toSing :: Demote k -> SomeSing k
    singInstance :: Sing (a :: k) -> SingInstance (a :: k)

-- | Implicit singletons
class Known a where
    getSing :: Sing a

-- | Witness for 'Known' dictionary
data SingInstance :: k -> Type where
    SingInstance :: Known a => SingInstance a

-- | Provide a singleton dictionary when an explicit singleton is at hand
withSingI :: SingKind k => Sing (a :: k) -> (Known a => r) -> r
withSingI (singInstance -> SingInstance) f = f

-- | Produce an explicit singleton from an implicit one
withSing :: Known a => (Sing a -> r) -> r
withSing f = f getSing

-- | Pass an ordinary data type into a function expecting a singleton
withSomeSing :: SingKind k => Demote k -> (forall (a :: k). Sing a -> r) -> r
withSomeSing (toSing -> SomeSing x) f = f x

{-# COMPLETE Sing #-}
pattern Sing :: forall k (a :: k) . SingKind k => Known a => Sing a
pattern Sing <- (singInstance -> SingInstance)

{-# COMPLETE FromSing #-}
pattern FromSing :: SingKind k => forall (a :: k). Sing a -> Demote k
pattern FromSing sng <- (toSing -> SomeSing sng)

-- | A dependent sum. The type of the second argument is determined by the value of the first.
data Sigma :: Type -> (s -> Type) -> Type where
  (:&:) :: Sing (fst :: s) -> t fst -> Sigma s t
infixr 4 :&:
