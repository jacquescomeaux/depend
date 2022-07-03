{-|
Module      : Fin
Description : The 'Fin' data type for bounded naturals
-}
module Fin
    ( Fin (..)
    ) where

import RIO

import Data.Kind (Type)

import Nat (Nat (..))


-- | A natural in the range [1, N]
type Fin :: Nat -> Type
data Fin n where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)
deriving instance Eq (Fin n)

-- | Catamorphism for 'Fin'
fin :: (forall m . r (Succ m)) -> (forall m . (r m -> r (Succ m))) -> Fin n -> r n
fin d _ FZ     = d
fin d f (FS n) = f (fin d f n)
