{-# LANGUAGE QuantifiedConstraints #-}
module Minimal where
import Data.Coerce
import Data.Kind (Type)



-- class (forall (a :: k) (b :: k). Coercible a b => Coercible (f a) (f b)) => F (f :: k -> Type)

-- class (forall (a :: k) (b :: k). Coercible a b => Coercible (forall (x :: i). f x a) (forall (x :: i). f x b)) => F (f :: i -> k -> Type)

-- class (forall (a :: Type). Ord a => Ord (forall (x :: Type). f x a)) => F (f :: Type -> Type -> Type)
