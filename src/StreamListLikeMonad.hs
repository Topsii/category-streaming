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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}

module StreamListLikeMonad where
import Prelude (IO, putStrLn, undefined)
import Prelude qualified
import Data.Bifunctor qualified as Base.Bifunctor
import Data.Coerce
import Data.Kind (Constraint, Type)
import Streaming.Internal hiding (concats, maps, yields)
import Control.Monad.Trans.Identity (IdentityT (..))
import Data.Proxy (Proxy(..))
import Control.Monad.Trans.Compose (ComposeT(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity ( Identity(..) )
import Data.Maybe (Maybe)
import Control.Monad qualified (join)
import qualified Control.Applicative
import Data.Either (Either (Left, Right))
import Data.Void (Void, absurd)
import Data.Functor.Product (Product (Pair))
import Data.Functor.Sum (Sum (InL, InR))

someFunc :: IO ()
someFunc = putStrLn "someFunc"


-- #########################################
-- definition of the classes Category, Functor and RelativeMonad
-- #########################################

type Morphism object_kind = object_kind -> object_kind -> Type

type Category :: forall {k}. Morphism k -> (k -> Constraint) -> Constraint
class Category morphism obj_constr | morphism -> obj_constr where
  id ::  obj_constr a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)

type Functor :: forall {i} {j}. Morphism i -> (i -> Constraint) -> Morphism j -> (j -> Constraint) -> (i -> j) -> Constraint
class
    ( Category src_morphism src_obj_constr
    , Category tgt_morphism tgt_obj_constr
    , forall a. src_obj_constr a => tgt_obj_constr (f a)
    )
    => Functor src_morphism src_obj_constr tgt_morphism tgt_obj_constr f where
  fmap :: (src_obj_constr  a, src_obj_constr b) => (a `src_morphism` b) -> (f a `tgt_morphism` f b)

type Bifunctor :: Morphism i -> (i -> Constraint) -> Morphism j -> (j -> Constraint) -> Morphism k -> (k -> Constraint) -> (i -> j -> k) -> Constraint
class
    ( Category src1_morphism src1_obj_constr
    , Category src2_morphism src2_obj_constr
    , Category tgt_morphism tgt_obj_constr
    , Functor src1_morphism src1_obj_constr (NatTrans src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr) (Functor src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr) p -- fmap = first
    , forall z. src1_obj_constr z => Functor src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr (p z) -- fmap = second
    , forall a b. (src1_obj_constr a, src2_obj_constr b) => tgt_obj_constr (p a b)
    )
    => Bifunctor src1_morphism src1_obj_constr src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr p | p tgt_morphism -> src1_morphism src2_morphism where

  bimap
    :: ( src1_obj_constr a
       , src1_obj_constr b
       , src2_obj_constr c
       , src2_obj_constr d
       )
    => (a `src1_morphism` b) -> (c `src2_morphism` d) -> p a c `tgt_morphism` p b d
  bimap f g = (runNat . fmap @src1_morphism @_ @(NatTrans src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr) @_) f . fmap g

  first
    :: ( src1_obj_constr a
       , src1_obj_constr b
       , src2_obj_constr c
       )
    => (a `src1_morphism` b) -> p a c `tgt_morphism` p b c
  first = runNat . fmap @src1_morphism @_ @(NatTrans src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr) @_

second
  :: ( Bifunctor src1_morphism src1_obj_constr src2_morphism src2_obj_constr tgt_morphism tgt_obj_constr p
     , src1_obj_constr a
     , src2_obj_constr c
     , src2_obj_constr d
     )
  => (c `src2_morphism` d) -> p a c `tgt_morphism` p a d
second = fmap


type TensorProduct k = k -> k -> k
type TensorUnit k = k

type MonoidalCategory :: forall {k}. Morphism k -> (k -> Constraint) -> TensorProduct k -> TensorUnit k -> Constraint
class ( Bifunctor morphism obj_constr morphism obj_constr morphism obj_constr m, Category morphism obj_constr) => MonoidalCategory morphism obj_constr m e | morphism m -> e where -- todo: remove this functional dependency by moving rassoc and lassoc to a superclass named Semicategory
    rassoc :: (obj_constr a, obj_constr b, obj_constr c) => ((a `m` b) `m` c) `morphism` (a `m` (b `m` c))
    lassoc :: (obj_constr a, obj_constr b, obj_constr c) => (a `m` (b `m` c)) `morphism` ((a `m` b) `m` c)
    rleftunit :: obj_constr a => (e `m` a) `morphism` a
    lleftunit :: obj_constr a => a `morphism` (e `m` a)
    rrightunit :: obj_constr a => (a `m` e) `morphism` a
    lrightunit :: obj_constr a => a `morphism` (a `m` e)

type MonoidInMonoidalCategory :: forall {k}. Morphism k -> (k -> Constraint) -> (k -> k -> k) -> k -> k -> Constraint
class (MonoidalCategory morphism obj_constr m e) => MonoidInMonoidalCategory morphism obj_constr m e a | a -> m morphism where
  mu :: (a `m` a) `morphism` a
  nu :: e `morphism` a

type VertComposition a b c = (b -> c) -> (a -> b) -> (a -> c)
type VertIdentity a = a -> a

-- Morphism (k -> k) denotes the category of endofunctors
-- a Monad is a monoid in the category of endofunctors where the
-- tensor product @m@ is composition and the tensor unit @e@ is identity
type Monad :: forall {k}. VertIdentity k -> VertComposition k k k -> Morphism (k -> k) -> ((k -> k) -> Constraint) -> (k -> k) -> Constraint
type Monad e m morphism obj_constr a = MonoidInMonoidalCategory morphism obj_constr m e a
-- type Monad :: VertIdentity k -> VertComposition k k k -> Morphism (k -> k) -> (k -> k) -> Constraint
-- class MonoidInMonoidalCategory e m morphism a => Monad e m morphism a where

-- type TwoCategory :: forall {k}. Morphism k -> Morphism (k -> k) -> Constraint
-- class (Category one_morphism, Category two_morphism) => TwoCategory one_morphism two_morphism | two_morphism -> one_morphism
-- type TwoCategory :: forall {k}. TensorUnit k -> TensorProduct k ->  VertIdentity k -> VertComposition k k k -> Morphism k -> Morphism (k -> k) -> Constraint
-- class
--     ( -- Category one_morphism
--     --, Category two_morphism
--       MonoidalCategory hor_e hor_p one_morphism
--     )
--     => TwoCategory hor_e hor_p vert_e vert_p (one_morphism :: k -> k -> Type) two_morphism | two_morphism -> one_morphism where
--   rexchange :: forall (a :: k) (b :: k) (c :: k) (d :: k). ((a `hor_p` b) `vert_p` (a `hor_p` b))`one_morphism` ((a `hor_p` b) `vert_p` (a `hor_p` b))
--   lexchange :: forall (a :: k) (b :: k) (c :: k) (d :: k). ((a `vert_p` b) `hor_p` (a `vert_p` b))`one_morphism` ((a `vert_p` b) `hor_p` (a `vert_p` b))

type HomCategory :: forall {k}. Morphism k -> (k -> Constraint) -> k -> k -> (k -> k) -> (k -> k) -> Type
newtype HomCategory morphism obj_constr a b f g = MkHomSet (f a `morphism` g b)

-- class (forall a b. Category (HomCategory one_morphism one_obj_constr a b) one_obj_constr) => TwoCategory one_morphism one_obj_constr two_morphism two_obj_constr | two_morphism -> one_morphism



class (MonoidalCategory two_morphism two_obj_constr p e) => VertComp e p one_morphism one_obj_constr two_morphism two_obj_constr | two_morphism -> p one_morphism where
  lvertComp :: Proxy two_morphism -> (one_obj_constr ((p f g) a), one_obj_constr (f (g a))) =>  (p f g) a `one_morphism` f (g a)
  rvertComp :: Proxy two_morphism -> (one_obj_constr (f (g a)), one_obj_constr ((p f g) a)) => f (g a) `one_morphism` (p f g) a
  -- lvertComp :: Proxy two_morphism -> (p f g) a `one_morphism` f (g a)
  -- rvertComp :: Proxy two_morphism -> f (g a) `one_morphism` (p f g) a

  lvertId :: Proxy two_morphism -> (one_obj_constr (e a), one_obj_constr a) => e a `one_morphism` a
  rvertId :: Proxy two_morphism -> (one_obj_constr (e a), one_obj_constr a) => a `one_morphism` e a

  lenriched :: Proxy two_morphism -> (two_obj_constr f, two_obj_constr g) => (forall a. (one_obj_constr (f a), one_obj_constr (g a)) => f a `one_morphism` g a) -> (f `two_morphism` g)
  renriched :: Proxy two_morphism -> (two_obj_constr f, two_obj_constr g) => (f `two_morphism` g) -> (forall a. (one_obj_constr (f a), one_obj_constr (g a)) => f a `one_morphism` g a)


type StrictMonad :: forall {k}. VertIdentity k -> VertComposition k k k -> Morphism k -> (k -> Constraint) -> Morphism (k -> k) -> ((k -> k) -> Constraint) -> (k -> k) -> Constraint
class
    ( --forall (a :: k). Coercible (e a) a
    --, forall (a :: k). Coercible ((p m m) a) (m (m a))
    --, forall (f :: k -> k) (g :: k -> k). Coercible (f `two_morphism` g) (NatCopy one_morphism f g) -- move this constraint to the definition of TwoCategory?
    --, forall (a :: k) (b :: k) (c :: k). Coercible a b => Coercible (a `one_morphism` c) (b `one_morphism` c)  -- is this constraint related to (.#) from the profunctor module? Basically this requires that one_morphism is a newtype whose first argument must not have the nominal role, see https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Coerce.html#t:Coercible
     Monad e p two_morphism two_obj_constr m
    , Category one_morphism one_obj_constr
    , VertComp e p one_morphism one_obj_constr two_morphism two_obj_constr
    -- , TwoCategory e' p' e p one_morphism one_obj_constr two_morphism two_obj_constr
    )
    => StrictMonad e p one_morphism one_obj_constr two_morphism two_obj_constr (m :: k -> k) where
  join :: forall a. (one_obj_constr (m (m a)), one_obj_constr (m a)) => (m (m a) `one_morphism` m a)
  -- join = coerce gg
  --   where
  --     gg :: (p m m) a `one_morphism` m a
  --     gg = coerce (mu @e @p @two_morphism @m)
  default join :: forall a. (one_obj_constr (m (m a)), one_obj_constr (m a), one_obj_constr (p m m a), two_obj_constr m, two_obj_constr (p m m)) => (m (m a) `one_morphism` m a)
  join
    = renriched @e @p @one_morphism @one_obj_constr @two_morphism @two_obj_constr (Proxy @two_morphism) mu
    . rvertComp @e @p @one_morphism @one_obj_constr @two_morphism @two_obj_constr (Proxy @two_morphism)

  returN :: forall a. (one_obj_constr a, one_obj_constr (m a)) => (a `one_morphism` m a)
  -- returN = coerce gg
  --   where
  --     gg :: e a `one_morphism` m a
  --     gg = coerce (nu @e @p @two_morphism @m)
  default returN :: forall a. (one_obj_constr a, one_obj_constr (m a), one_obj_constr (e a), two_obj_constr m, two_obj_constr e) => (a `one_morphism` m a)
  returN
    = renriched @e @p @one_morphism @one_obj_constr @two_morphism @two_obj_constr (Proxy @two_morphism) nu
    . rvertId @e @p @one_morphism @one_obj_constr @two_morphism @two_obj_constr (Proxy @two_morphism)

-- https://ncatlab.org/nlab/show/relative+monad#idea
type RelativeMonad :: forall {i} {j}. Morphism i -> (i -> Constraint) -> Morphism j -> (j -> Constraint) -> (i -> j) -> (i -> j) -> Constraint
class (Functor src_morphism src_obj_constr tgt_morphism tgt_obj_constr j, Functor src_morphism src_obj_constr tgt_morphism tgt_obj_constr m) => RelativeMonad src_morphism src_obj_constr tgt_morphism tgt_obj_constr j m | m tgt_morphism -> src_morphism, m -> j where
  pure :: src_obj_constr a => j a `tgt_morphism` m a
  (=<<) :: (src_obj_constr a, src_obj_constr b) => (j a `tgt_morphism` m b) -> (m a `tgt_morphism` m b)


-- #########################################
-- instances for the normal function type (->)
-- #########################################

instance Category (->) Vac where
  id = Prelude.id
  (.) = (Prelude..)

type Vacuous :: i -> Constraint
class Vacuous a
instance Vacuous a

type Vac :: i -> Constraint
type Vac = Vacuous

-- #########################################
-- instances for Op, the opposite category
-- #########################################

type Op :: Morphism k -> k -> k -> Type
newtype Op morphism a b = Op (morphism b a)


-- #########################################
-- instances for Flip
-- #########################################

type Flip :: (i -> j -> Type) -> j -> i -> Type
newtype Flip p a b = Flip { runFlip :: p b a }

instance Category morphism obj_constr => Category (Flip morphism) obj_constr where
  id = Flip id
  (.) (Flip f) (Flip g) = Flip (g . f)

-- #########################################
-- MonoidalCategory with flipped tensor product

instance Functor (->) Vac Nat NatConstr p => Functor (->) Vac (->) Vac (Flip p a) where
  fmap f = Flip . runNat (fmap @(->) @Vac @Nat @NatConstr f) . runFlip

instance (Functor (->) Vac Nat NatConstr p) => Functor (->) Vac Nat NatConstr (Flip p) where
  fmap f = Nat (Flip . fmap f . runFlip)

instance (Bifunctor (->) Vac (->) Vac (->) Vac p) => Bifunctor (->) Vac (->) Vac (->) Vac  (Flip p) where

instance MonoidalCategory (->) Vac m e => MonoidalCategory (->) Vac (Flip m) e where
  rassoc = Flip . first Flip . lassoc . second runFlip . runFlip
  lassoc = Flip . second Flip . rassoc . first runFlip . runFlip
  rleftunit = rrightunit . runFlip
  lleftunit = Flip . lrightunit
  rrightunit = rleftunit . runFlip
  lrightunit = Flip . lleftunit

-- #########################################
-- MonoidalCategory instance with opposite category

instance (Functor (->) Vac (->) Vac (p a)) => Functor (Flip (->)) Vac (Flip (->)) Vac (p a) where
  fmap = Flip . fmap . runFlip

instance (Functor (->) Vac Nat NatConstr p)
    => Functor (Flip (->)) Vac (NatTrans (Flip (->)) Vac (Flip (->)) Vac) (Functor (Flip (->)) Vac (Flip (->)) Vac) p
    where
  fmap f = Nat (Flip (runNat (fmap @(->) @_ @Nat @_ (runFlip f))))

instance
    ( Bifunctor (->) Vac (->) Vac (->) Vac p
    )
    => Bifunctor (Flip (->)) Vac (Flip (->)) Vac (Flip (->)) Vac p

instance (MonoidalCategory (->) Vac m e) => MonoidalCategory (Flip (->)) Vac m e where
  rassoc = Flip lassoc
  lassoc = Flip rassoc
  rleftunit = Flip lleftunit
  lleftunit = Flip rleftunit
  rrightunit = Flip lrightunit
  lrightunit = Flip rrightunit


-- #########################################
-- instances for Flip1
-- #########################################

type Flip1 :: (i -> j -> k -> Type) -> j -> i -> k -> Type
newtype Flip1 p f g a = Flip1 { runFlip1 :: p g f a }

instance (Functor (->) Vac (->) Vac (p a b)) => Functor (->) Vac (->) Vac (Flip1 p b a) where
  fmap f = Flip1 . fmap f . runFlip1

instance -- first to second
    ( Functor (->) Vac (->) Vac b
    , Functor Nat NatConstr NatNat NatNatConstr p
    )
    => Functor Nat NatConstr Nat NatConstr (Flip1 p b) where
  fmap f = Nat (Flip1 . runNat (runNat (fmap @Nat @NatConstr @NatNat @NatNatConstr f)) . runFlip1)

instance -- second to first
    ( Functor Nat NatConstr NatNat NatNatConstr p
    )
    => Functor Nat NatConstr NatNat NatNatConstr (Flip1 p) where
  fmap f = Nat (Nat (Flip1 . runNat (fmap @Nat @NatConstr @Nat @NatConstr f) . runFlip1))

instance
    ( Bifunctor Nat NatConstr Nat NatConstr Nat NatConstr p
    )
    => Bifunctor Nat NatConstr Nat NatConstr Nat NatConstr (Flip1 p) where


bimapFlippedProduct
  ::
    ( Functor (->) Vac (->) Vac a
    , Functor (->) Vac (->) Vac b
    , Functor (->) Vac (->) Vac c
    , Functor (->) Vac (->) Vac d
    )
  => Nat a c
  -> Nat b d
  -> Nat
      (Flip1 Product a b)
      (Flip1 Product c d)
bimapFlippedProduct = bimap @(Type -> Type) @(Type -> Type) @(Type -> Type) @Nat @_ @Nat @_ @Nat @_ @(Flip1 Product)


lassocFlipped2 = lassoc @(Flip (->)) @Vac @(Flip (,)) @()


-- #########################################
-- definition of natural transformation (Nat) and its Category instance
-- #########################################

type Nat :: Morphism (Type -> Type)
type Nat = NatTrans (->) Vac (->) Vac

type NatNat :: Morphism ((Type -> Type) -> (Type -> Type))
type NatNat = NatTrans Nat NatConstr Nat NatConstr
type NatNatNat = NatTrans NatNat NatNatConstr NatNat NatNatConstr

type NatConstr = Functor (->) Vac (->) Vac
type NatNatConstr = Functor Nat NatConstr Nat NatConstr
type NatNatNatConstr = Functor NatNat NatNatConstr NatNat NatNatConstr

type NatTrans :: forall {i} {k}. Morphism i -> (i -> Constraint) -> Morphism k -> (k -> Constraint) -> Morphism (i -> k)
data NatTrans src_morphism src_obj_constr tgt_morphism tgt_obj_constr f g where
  -- Nat :: (Functor src_morphism tgt_morphism f, Functor src_morphism tgt_morphism g) => { runNat :: forall a. src_obj_constr a => tgt_morphism (f a) (g a) } -> NatTrans src_morphism tgt_morphism f g
  Nat :: Functor src_morphism src_obj_constr tgt_morphism tgt_obj_constr f => { runNat :: forall a. src_obj_constr a => tgt_morphism (f a) (g a) } -> NatTrans src_morphism src_obj_constr tgt_morphism tgt_obj_constr f g
  -- Nat :: { runNat :: forall a. obj_constr a => morphism (f a) (g a) } -> NatTrans morphism f g

instance (Category src_morphism src_obj_constr, Category tgt_morphism tgt_obj_constr) => Category (NatTrans (src_morphism :: Morphism i) src_obj_constr (tgt_morphism :: Morphism k) tgt_obj_constr :: Morphism (i -> k)) (Functor src_morphism src_obj_constr tgt_morphism tgt_obj_constr) where
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)

instance MonoidalCategory Nat NatConstr Compose Identity where
  -- in case of the assoc and rightunit conversions we need to utilize the Functor instance of the most outer functor, because the role of its type argument could be nominal
  rassoc = Nat (Compose . fmap Compose . getCompose . getCompose)
  lassoc =  Nat (Compose . Compose . fmap getCompose . getCompose)
  rleftunit = Nat (runIdentity . getCompose)
  lleftunit = Nat (Compose . Identity)
  rrightunit = Nat (fmap runIdentity . getCompose)
  lrightunit = Nat (Compose . fmap Identity)

instance VertComp Identity Compose (->) Vac Nat NatConstr where
  lvertComp _ = getCompose
  rvertComp _ = Compose
  lvertId _ = runIdentity
  rvertId _ = Identity
  lenriched _ f = Nat f
  renriched _ f = runNat f


-- #########################################
-- instances for Compose
-- #########################################

instance (Functor (->) Vac (->) Vac f, Functor (->) Vac (->) Vac g) => Functor (->) Vac (->) Vac (Compose f g) where
  fmap f = Compose . fmap (fmap @(->) @_ @(->) @_ f) . getCompose

instance Functor (->) Vac (->) Vac t => Functor Nat NatConstr Nat NatConstr (Compose t) where
  fmap (Nat f) = Nat (Compose . fmap f . getCompose)

instance Functor Nat NatConstr NatNat NatNatConstr Compose where
  fmap (Nat f) = Nat (Nat (Compose . f . getCompose))

instance Bifunctor Nat NatConstr Nat NatConstr Nat NatConstr Compose where
  bimap (Nat f) (Nat g) = Nat (Compose . f . fmap g . getCompose)
  first (Nat f) = Nat (Compose . f . getCompose)


-- #########################################
-- instances for Identity
-- #########################################

instance Functor (->) Vac (->) Vac Identity where
  fmap f (Identity x) = Identity (f x)


-- #########################################
-- definition of transformations of natural transformation (NatNat) and its Category instance
-- #########################################

fmap2 :: forall f a b. (Functor Nat NatConstr Nat NatConstr f, Functor (->) Vac (->) Vac a,  Functor (->) Vac (->) Vac b) => (forall x. a x -> b x) -> (forall x. f a x -> f b x)
fmap2 f = runNat (fmap @Nat @NatConstr @Nat @NatConstr @f @a @b (Nat f))

instance MonoidalCategory NatNat NatNatConstr ComposeT IdentityT where
  rassoc = Nat (Nat (ComposeT . fmap2 ComposeT . getComposeT . getComposeT))
  lassoc = Nat (Nat (ComposeT . ComposeT . fmap2 getComposeT . getComposeT))
  rleftunit = Nat (Nat (runIdentityT . getComposeT))
  lleftunit = Nat (Nat (ComposeT . IdentityT))
  rrightunit = Nat (Nat (fmap2 runIdentityT . getComposeT))
  lrightunit = Nat (Nat (ComposeT . fmap2 IdentityT))

instance VertComp IdentityT ComposeT Nat NatConstr NatNat NatNatConstr where
  lvertComp _ = Nat getComposeT
  rvertComp _ = Nat ComposeT
  lvertId _ = Nat runIdentityT
  rvertId _ = Nat IdentityT
  lenriched _ f = Nat f
  -- renriched _ f = runNat f


-- #########################################
-- instances for ComposeT
-- #########################################

instance Functor (->) Vac (->) Vac (f (g a)) => Functor (->) Vac (->) Vac (ComposeT f g a) where
  fmap :: forall x y. (x -> y) -> ComposeT f g a x -> ComposeT f g a y
  fmap = coerce (fmap @(->) @Vac @(->) @Vac @(f (g a)) @x @y)

instance (Functor Nat NatConstr Nat NatConstr f, Functor Nat NatConstr Nat NatConstr g) => Functor Nat NatConstr Nat NatConstr (ComposeT f g) where
  fmap (Nat f) = Nat (\(ComposeT x) -> ComposeT (fmap2 (fmap2 f) x))

instance Functor Nat NatConstr Nat NatConstr z => Functor NatNat NatNatConstr NatNat NatNatConstr (ComposeT z) where
  fmap (Nat f) = Nat (Nat (ComposeT . fmap2 (runNat f) . getComposeT))

instance Functor NatNat NatNatConstr NatNatNat NatNatNatConstr ComposeT where
  fmap (Nat f) = Nat (Nat (Nat (ComposeT . runNat f . getComposeT)))

instance Bifunctor NatNat NatNatConstr NatNat NatNatConstr NatNat NatNatConstr ComposeT where
  bimap (Nat f) (Nat g) = Nat (Nat (ComposeT . runNat f . fmap2 (runNat g) . getComposeT))
  first (Nat f) = Nat (Nat (ComposeT . runNat f . getComposeT))


-- #########################################
-- instances for IdentityT
-- #########################################

instance Functor Nat NatConstr Nat NatConstr IdentityT where
  fmap (Nat f) = Nat (IdentityT . f . runIdentityT)

instance Functor (->) Vac (->) Vac f => Functor (->) Vac (->) Vac (IdentityT f) where
  fmap func = coerce (fmap @(->) @_ @(->) @_ @f func)


-- #########################################
-- monoidal category instances for (,) in the category (->)
-- #########################################

instance Functor (->) Vac (->) Vac ((,) a) where
  fmap = Prelude.fmap

instance Functor (->) Vac Nat NatConstr (,) where
  fmap f = Nat (Base.Bifunctor.first f)

instance Bifunctor (->) Vac (->) Vac (->) Vac (,) where
  bimap = Base.Bifunctor.bimap
  first = Base.Bifunctor.first

instance MonoidalCategory (->) Vac (,) () where
  rassoc ((a, b), c) = (a, (b, c))
  lassoc (a, (b, c)) = ((a, b), c)
  rleftunit ((), a) = a
  lleftunit a = ((), a)
  rrightunit (a, ()) = a
  lrightunit a = (a, ())


-- #########################################
-- monoidal category instances for Either in the category (->)
-- #########################################

instance Functor (->) Vac (->) Vac (Either a) where
  fmap = Prelude.fmap

instance Functor (->) Vac Nat NatConstr Either where
  fmap f = Nat (Base.Bifunctor.first f)

instance Bifunctor (->) Vac (->) Vac (->) Vac Either where
  bimap = Base.Bifunctor.bimap
  first = Base.Bifunctor.first

instance MonoidalCategory (->) Vac Either Void where
  rassoc = \case
    Left (Left a)  -> Left a
    Left (Right b) -> Right (Left b)
    Right c        -> Right (Right c)
  lassoc = \case
    Left a          -> Left (Left a)
    Right (Left b)  -> Left (Right b)
    Right (Right c) -> Right c
  rleftunit = Prelude.either absurd id
  lleftunit = Right
  rrightunit = Prelude.either id absurd
  lrightunit = Left


-- #########################################
-- monoidal category instances for Product in the category Nat
-- #########################################

instance (Functor (->) Vac (->) Vac f, Functor (->) Vac (->) Vac g) => Functor (->) Vac (->) Vac (Product f g) where
  fmap f (Pair fa ga) = Pair (fmap f fa) (fmap f ga)

instance (Functor (->) Vac (->) Vac a) => Functor Nat NatConstr Nat NatConstr (Product a) where
  fmap (Nat f) = Nat (\(Pair x y) -> Pair x (f y))

instance Functor Nat NatConstr NatNat NatNatConstr Product where
  fmap (Nat f) = Nat (Nat (\(Pair x y) -> Pair (f x) y))

instance Bifunctor Nat NatConstr Nat NatConstr Nat NatConstr Product where
  bimap (Nat f) (Nat g) = Nat (\(Pair x y) -> Pair (f x) (g y))
  first (Nat f) = Nat (\(Pair x y) -> Pair (f x) y)

instance Functor (->) Vac (->) Vac Proxy where
  fmap _f Proxy = Proxy

instance MonoidalCategory Nat NatConstr Product Proxy where
  rassoc = Nat (\(Pair (Pair a b) c) -> Pair a (Pair b c))
  lassoc = Nat (\(Pair a (Pair b c)) -> Pair (Pair a b) c)
  rleftunit = Nat (\(Pair Proxy a) -> a)
  lleftunit = Nat (Pair Proxy)
  rrightunit = Nat (\(Pair a Proxy) -> a)
  lrightunit = Nat (`Pair` Proxy)


-- #########################################
-- monoidal category instances for Sum in the category Nat
-- #########################################

instance (Functor (->) Vac (->) Vac f, Functor (->) Vac (->) Vac g) => Functor (->) Vac (->) Vac (Sum f g) where
  fmap f = \case
    InL fa -> InL (fmap f fa)
    InR ga -> InR (fmap f ga)

instance (Functor (->) Vac (->) Vac a) => Functor Nat NatConstr Nat NatConstr (Sum a) where
  fmap (Nat f) = Nat (\case
    InL ax -> InL ax
    InR bx -> InR (f bx))

instance Functor Nat NatConstr NatNat NatNatConstr Sum where
  fmap (Nat f) = Nat (Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR bx))

instance Bifunctor Nat NatConstr Nat NatConstr Nat NatConstr Sum where
  bimap (Nat f) (Nat g) = Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR (g bx))
  first (Nat f) = Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR bx)

data Void1 a

absurd1 :: Void1 x -> b
absurd1 v = case v of {}

instance Functor (->) Vac (->) Vac Void1 where
  fmap _f = absurd1

instance MonoidalCategory Nat NatConstr Sum Void1 where
  rassoc = Nat (\case
    InL (InL a) -> InL a
    InL (InR b) -> InR (InL b)
    InR c       -> InR (InR c))
  lassoc = Nat (\case
    InL a       -> InL (InL a)
    InR (InL b) -> InL (InR b)
    InR (InR c) -> InR c)
  rleftunit = Nat (\case
    InL v -> absurd1 v
    InR a -> a)
  lleftunit = Nat InR
  rrightunit = Nat (\case
    InL a -> a
    InR v -> absurd1 v)
  lrightunit = Nat InL


-- #########################################
-- instances for familiar Monads such as Maybe or IO
-- #########################################

instance Prelude.Monad m => Functor (->) Vac (->) Vac (Control.Applicative.WrappedMonad m) where
  fmap = Prelude.fmap . coerce
instance Prelude.Monad m => MonoidInMonoidalCategory Nat NatConstr Compose Identity (Control.Applicative.WrappedMonad m) where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)

instance Prelude.Monad m => StrictMonad Identity Compose (->) Vac Nat NatConstr (Control.Applicative.WrappedMonad m)

instance Functor (->) Vac (->) Vac IO where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Nat NatConstr Compose Identity IO where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Vac Nat NatConstr IO

instance Functor (->) Vac (->) Vac Maybe where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Nat NatConstr Compose Identity Maybe where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Vac Nat NatConstr Maybe


-- #########################################
-- definition of StreamFlip and its instances
-- #########################################

-- flips type parameters m and f
newtype StreamFlip m f r = MkStreamFlip { getStream :: Stream f m r }

instance (Functor (->) Vac (->) Vac f, Prelude.Monad m) => Functor (->) Vac (->) Vac (StreamFlip m f) where
  fmap = coerce (fmap @(->) @_ @(->) @_ @(Stream f m))

instance (Prelude.Monad m) => Functor Nat NatConstr Nat NatConstr (StreamFlip m) where
  fmap (Nat f) = Nat (coerce (maps @m f))

instance (Prelude.Monad m) => RelativeMonad Nat NatConstr Nat NatConstr IdentityT (StreamFlip m) where
  pure = Nat (coerce yields)
  (=<<) (Nat f) = Nat (coerce (concats @_ @m . maps @m @_ @(Stream _ m) (coerce f)))

instance (Functor (->) Vac (->) Vac f, Prelude.Monad m) => MonoidInMonoidalCategory Nat NatConstr Compose Identity (StreamFlip m f) where
  mu = Nat (MkStreamFlip . joinStream . fmap getStream . getStream . getCompose)
  nu = Nat (MkStreamFlip . Return . runIdentity)

instance (Prelude.Monad m) => MonoidInMonoidalCategory NatNat NatNatConstr ComposeT IdentityT (StreamFlip m) where
  mu = Nat (Nat (coerce (concats . maps coerce)))
  nu = Nat (Nat (coerce yields))

instance (Prelude.Monad m) => StrictMonad IdentityT ComposeT Nat NatConstr NatNat NatNatConstr (StreamFlip m) where


-- #########################################
-- definitions for Stream
-- #########################################


-- Functor instance

instance (Functor (->) Vac (->) Vac f, Prelude.Monad m) => Functor (->) Vac (->) Vac (Stream f m) where
  fmap f = loop where
    loop stream = case stream of
      Return r -> Return (f r)
      Effect m -> Effect (do {stream' <- m; Prelude.return (loop stream')})
      Step   g -> Step (fmap loop g)
  {-# INLINABLE fmap #-}


-- copypasted definitions that were changed to
-- require Functor (->) Vac (->) Vac f instead of Prelude.Functor f

maps :: (Prelude.Monad m, Functor (->) Vac (->) Vac f) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
maps phi = loop where
  loop stream = case stream of
    Return r -> Return r
    Effect m -> Effect (Prelude.fmap loop m)
    Step   f -> Step (phi (fmap loop f))
{-# INLINABLE maps #-}

concats :: forall f m r. (Prelude.Monad m, Functor (->) Vac (->) Vac f) => Stream (Stream f m) m r -> Stream f m r
concats = loop where
  loop :: Stream (Stream f m) m r -> Stream f m r
  loop stream = case stream of
    Return r -> Return r
    Effect m -> (Effect . Prelude.fmap Return) m `bindStream` loop
    Step fs  -> fs `bindStream` loop
{-# INLINE concats #-}

bindStream :: (Prelude.Monad m, Functor (->) Vac (->) Vac f) => Stream f m t -> (t -> Stream f m r) -> Stream f m r
stream `bindStream` f =
  loop stream where
  loop stream0 = case stream0 of
    Step fstr -> Step (fmap loop fstr)
    Effect m  -> Effect (Prelude.fmap loop m)
    Return r  -> f r
{-# INLINABLE bindStream #-}

joinStream :: (Prelude.Monad m, Functor (->) Vac (->) Vac f) => Stream f m (Stream f m r) -> Stream f m r
joinStream stream = bindStream stream id

yields :: (Prelude.Monad m, Functor (->) Vac (->) Vac f) => f r -> Stream f m r
yields fr = Step (fmap Return fr)
{-# INLINE yields #-}