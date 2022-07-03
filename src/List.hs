{-|
Module      : List
Description : Helper definitions for working with type-level lists
-}
-- {-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
module List
    ( ListLen (..)
    , KnownListLen (..)
    , LElem (..)
    , type (++)
    , Replicate
    , Length
    , All
    , Map
    , Concat
    , SList (..)
    ) where

import RIO hiding (Map)

import Data.Kind (Type, Constraint)

import Nat (Nat (..))
import Singletons (Sing)


-- | Singletons for lists
type SList :: forall k . [k] -> Type
data SList :: [k] -> Type where
    SNil :: SList '[]
    (:%) :: Sing t -> SList ts -> SList (t : ts)
infixr 5 :%

-- | Structural recursion helper for lists
data ListLen :: [k] -> Type where
    LZ :: ListLen '[]
    LS :: KnownListLen ts => ListLen (t : ts)

class KnownListLen (ts :: [k]) where
    getListLen :: ListLen ts

instance KnownListLen '[] where
    getListLen = LZ

instance KnownListLen ts => KnownListLen (t : ts) where
    getListLen = LS

-- | Witness that an element is contained in a list
data LElem :: forall a . [a] -> a -> Type where
    LEZ :: LElem (x : xs) x
    LES :: LElem xs x -> LElem (y : xs) x

deriving instance Show (LElem xs x)

-- | Append two type-level lists
type family (++) (as :: [k]) (bs :: [k]) :: [k] where
    (++) '[] bs      = bs
    (++) (a : as) bs = a : (as ++ bs)

-- | 'Replicate' @n@ @a@ is type level list of length @n@, with @a@ the value of every element
type family Replicate (n :: Nat) (a :: k) :: [k] where
    Replicate Zero a     = '[]
    Replicate (Succ n) a = a : Replicate n a

-- | Get the length of a type-level list
type family Length (ts :: [k]) :: Nat where
    Length '[]      = Zero
    Length (_ : ts) = Succ (Length ts)

-- TODO catamorphism

-- | Apply a constraint to every element of a list
type family All (c :: k -> Constraint) (ts :: [k]) :: Constraint where
    All c '[]      = ()
    All c (t : ts) = (c t, All c ts)

-- | Map a type-level function over a list
type family Map (f :: h -> k) (ts :: [h]) :: [k] where
    Map f '[]      = '[]
    Map f (t : ts) = f t : Map f ts

-- | Join a type-level list of lists into one
-- needs UndecidableInstances
type Concat :: [[k]] -> [k]
type family Concat bss where
    Concat '[]        = '[]
    Concat (bs : bss) = bs ++ Concat bss
