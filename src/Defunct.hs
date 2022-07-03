{-# LANGUAGE UndecidableInstances #-}
module Defunct where

import Data.Kind (Type)


data TyFun a b
type a ~> b = TyFun a b -> Type
infixr 0 ~>
type family Apply (f :: TyFun a b -> Type) (x :: a) :: b
type f @@ a = Apply f a
infixl 9 @@

data Id :: a ~> a
type instance Apply Id x = x

data TyCon1 :: (j -> k) -> (j ~> k)
data TyCon2 :: (h -> j -> k) -> (h ~> j ~> k)

type instance Apply (TyCon1 t) a = t a
type instance Apply (TyCon2 t) a = TyCon1 (t a)

data Compose :: (b ~> c) -> (a ~> b) -> (a ~> c)
type instance Apply (Compose f g) x = f @@ (g @@ x)

data (.) :: (b ~> c) -> (a ~> b) -> (a ~> c)
type instance Apply (f . g) x = f @@ (g @@ x)
