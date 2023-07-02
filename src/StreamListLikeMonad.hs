{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ConstraintKinds #-}
 
module StreamListLikeMonad
    ( someFunc
    ) where
import Prelude (IO, putStrLn, return)
import Prelude qualified
import Data.Coerce
import Data.Kind (Constraint, Type)
import Streaming.Internal hiding (concats, maps, yields)
import Control.Monad.Trans.Identity (IdentityT (..))
 
someFunc :: IO ()
someFunc = putStrLn "someFunc"
 
 
-- #########################################
-- definition of the classes Category, Functor and RelativeMonad
-- #########################################
 
type Morphism object_kind = object_kind -> object_kind -> Type
 
type Category :: Morphism k -> Constraint
class Category morphism where
  type ObjectConstraint morphism :: i -> Constraint
  id :: ObjectConstraint morphism a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)
 
 
type Functor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class (Category src_morphism, Category tgt_morphism) => Functor src_morphism tgt_morphism f | f -> src_morphism tgt_morphism where
  fmap :: ObjectConstraint src_morphism a => (a `src_morphism` b) -> (f a `tgt_morphism` f b)
 
 
-- https://ncatlab.org/nlab/show/relative+monad#idea
type RelativeMonad :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> (i -> j) -> Constraint
class (Functor src_morphism tgt_morphism j, Functor src_morphism tgt_morphism m) => RelativeMonad src_morphism tgt_morphism j m | m -> j where
  pure :: ObjectConstraint src_morphism a => j a `tgt_morphism` m a
  (=<<) :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => (j a `tgt_morphism` m b) -> (m a `tgt_morphism` m b)
 
 
-- #########################################
-- definition of natural transformation (Nat) and its Category instance
-- #########################################
 
type Nat :: (Type -> Type) -> (Type -> Type) -> Type
newtype Nat f g = Nat (forall a. (->) (f a) (g a))
        
instance Category Nat where
  type ObjectConstraint Nat = Functor (->) (->)
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)
 
  
-- #########################################
-- definition of the category instance for the normal function type (->)
-- #########################################
 
instance Category (->) where
  type ObjectConstraint (->) = Vacuous (->)
  id = Prelude.id
  (.) = (Prelude..)
 
type Vacuous :: Morphism i -> i -> Constraint
class Vacuous c a
instance Vacuous c a
 
 
-- #########################################
-- instances for IdentityT
-- #########################################
 
instance Functor Nat Nat IdentityT where
  fmap :: forall a b. Nat a b -> Nat (IdentityT a) (IdentityT b)
  fmap (Nat f) = Nat (IdentityT . f . runIdentityT :: forall x. IdentityT a x -> IdentityT b x)
 
instance Functor (->) (->) f => Functor (->) (->) (IdentityT f) where
  fmap func = coerce (fmap @(->) @(->) @f func)
  
 
-- #########################################
-- definition of StreamFlip and its instances
-- #########################################
 
-- flips type parameters m and f
newtype StreamFlip m f r = MkStreamFlip { getStream :: Stream f m r }
 
instance (Functor (->) (->) f, Prelude.Monad m) => Functor (->) (->) (StreamFlip m f) where
  fmap = coerce (fmap @(->) @(->) @(Stream f m))
 
instance (Prelude.Monad m) => Functor Nat Nat (StreamFlip m) where
  fmap (Nat f) = Nat (coerce (maps @m f))
 
instance (Prelude.Monad m) => RelativeMonad Nat Nat IdentityT (StreamFlip m) where
  pure = Nat (coerce yields)
  (=<<) (Nat f) = Nat (coerce (concats @_ @m . maps @m @_ @(Stream _ m) (coerce f)))
 
 
-- #########################################
-- definitions for Stream
-- #########################################
 
 
-- Functor instance
 
instance (Functor (->) (->) f, Prelude.Monad m) => Functor (->) (->) (Stream f m) where
  fmap f = loop where
    loop stream = case stream of
      Return r -> Return (f r)
      Effect m -> Effect (do {stream' <- m; return (loop stream')})
      Step   g -> Step (fmap loop g)
  {-# INLINABLE fmap #-}
 
 
-- copypasted definitions that were changed to 
-- require Functor (->) (->) f instead of Prelude.Functor f
 
maps :: (Prelude.Monad m, Functor (->) (->) f) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
maps phi = loop where
  loop stream = case stream of
    Return r -> Return r
    Effect m -> Effect (Prelude.fmap loop m)
    Step   f -> Step (phi (fmap loop f))
{-# INLINABLE maps #-}
 
concats :: forall f m r. (Prelude.Monad m, Functor (->) (->) f) => Stream (Stream f m) m r -> Stream f m r
concats = loop where
  loop :: Stream (Stream f m) m r -> Stream f m r
  loop stream = case stream of
    Return r -> Return r
    Effect m -> (Effect . Prelude.fmap Return) m `bindStream` loop
    Step fs  -> fs `bindStream` loop
{-# INLINE concats #-}
 
bindStream :: (Prelude.Monad m, Functor (->) (->) f) => Stream f m t -> (t -> Stream f m r) -> Stream f m r
stream `bindStream` f =
  loop stream where
  loop stream0 = case stream0 of
    Step fstr -> Step (fmap loop fstr)
    Effect m  -> Effect (Prelude.fmap loop m)
    Return r  -> f r
{-# INLINABLE bindStream #-}
 
yields :: (Prelude.Monad m, Functor (->) (->) f) => f r -> Stream f m r
yields fr = Step (fmap Return fr)
{-# INLINE yields #-}