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
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QualifiedDo #-}

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
import Data.Type.Equality ( type (~) )
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

type Category :: forall {k}. Morphism k -> Constraint
class Category morphism where
  type ObjectConstraint morphism :: i -> Constraint
  id :: ObjectConstraint morphism a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)

type Functor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class
    ( Category src_morphism
    , Category tgt_morphism
    -- , forall a. ObjectConstraint src_morphism a => ObjectConstraint tgt_morphism (f a)
    -- the line above does not work, instead we use the workaround from https://gitlab.haskell.org/ghc/ghc/-/issues/14860#note_495352 in the line below:
    , forall a. (ObjectConstraint src_morphism a) => Obj tgt_morphism (f a)
    )
    => Functor src_morphism tgt_morphism f where
  fmap :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => (a `src_morphism` b) -> (f a `tgt_morphism` f b)

class    (ObjectConstraint x a) => Obj x a
instance (ObjectConstraint x a) => Obj x a

type Bifunctor :: Morphism i -> Morphism j -> Morphism k -> (i -> j -> k) -> Constraint
class
    ( Category src1_morphism
    , Category src2_morphism
    , Category tgt_morphism
    , Functor src1_morphism (Transformation src2_morphism tgt_morphism) p -- fmap = first
    , forall z. ObjectConstraint src1_morphism z => Functor src2_morphism tgt_morphism (p z) -- fmap = second
    -- , forall a b. (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => ObjectConstraint tgt_morphism (p a b)
    -- the line above does not work, instead we use the workaround from https://gitlab.haskell.org/ghc/ghc/-/issues/14860#note_495352 in the line below:
    , forall a b. (ObjectConstraint src1_morphism a, ObjectConstraint src2_morphism b) => Obj tgt_morphism (p a b)
    )
    => Bifunctor src1_morphism src2_morphism tgt_morphism p | p tgt_morphism -> src1_morphism src2_morphism where

  bimap
    :: ( ObjectConstraint src1_morphism a
       , ObjectConstraint src1_morphism b
       , ObjectConstraint src2_morphism c
       , ObjectConstraint src2_morphism d
       )
    => (a `src1_morphism` b) -> (c `src2_morphism` d) -> p a c `tgt_morphism` p b d
  bimap f g = (runTrans . fmap @src1_morphism @(Transformation src2_morphism tgt_morphism)) f . fmap g

  first
    :: ( ObjectConstraint src1_morphism a
       , ObjectConstraint src1_morphism b
       , ObjectConstraint src2_morphism c
       )
    => (a `src1_morphism` b) -> p a c `tgt_morphism` p b c
  first = runTrans . fmap @src1_morphism @(Transformation src2_morphism tgt_morphism)

second
  :: ( Bifunctor src1_morphism src2_morphism tgt_morphism p
     , ObjectConstraint src1_morphism a
     , ObjectConstraint src2_morphism b
     , ObjectConstraint src2_morphism c
     )
  => (b `src2_morphism` c) -> p a b `tgt_morphism` p a c
second = fmap

type ContravariantFunctor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class Functor (Flip src_morphism) tgt_morphism f => ContravariantFunctor src_morphism tgt_morphism f where
  contramap :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => (b `src_morphism` a) -> (f a `tgt_morphism` f b)
  contramap f = fmap @(Flip src_morphism) @tgt_morphism @f (Flip f)

type Profunctor :: Morphism i -> Morphism j -> Morphism k -> (i -> j -> k) -> Constraint
class (Bifunctor (Flip src1_morphism) src2_morphism tgt_morphism p) => Profunctor src1_morphism src2_morphism tgt_morphism p | p tgt_morphism -> src1_morphism src2_morphism where

  dimap
    :: ( ObjectConstraint src1_morphism a
       , ObjectConstraint src1_morphism b
       , ObjectConstraint src2_morphism c
       , ObjectConstraint src2_morphism d
       )
    => (b `src1_morphism` a) -> (c `src2_morphism` d) -> p a c `tgt_morphism` p b d
  dimap f g = (runTrans . fmap @(Flip src1_morphism) @(Transformation src2_morphism tgt_morphism)) (Flip f) . fmap g

  lmap
    :: ( ObjectConstraint src1_morphism a
       , ObjectConstraint src1_morphism b
       , ObjectConstraint src2_morphism c
       )
    => (b `src1_morphism` a) -> p a c `tgt_morphism` p b c
  lmap f = dimap f id

rmap
  :: ( Profunctor src1_morphism src2_morphism tgt_morphism p
     , ObjectConstraint src1_morphism a
     , ObjectConstraint src2_morphism b
     , ObjectConstraint src2_morphism c
     )
  => (b `src2_morphism` c) -> p a b `tgt_morphism` p a c
rmap = fmap

type BicontravariantFunctor :: Morphism i -> Morphism j -> Morphism k -> (i -> j -> k) -> Constraint
class Bifunctor (Flip src1_morphism) (Flip src2_morphism) tgt_morphism p => BicontravariantFunctor src1_morphism src2_morphism tgt_morphism p where
  bicontramap
    :: ( ObjectConstraint src1_morphism a
       , ObjectConstraint src1_morphism b
       , ObjectConstraint src2_morphism c
       , ObjectConstraint src2_morphism d
       )
    => (b `src1_morphism` a) -> (d `src2_morphism` c) -> p a c `tgt_morphism` p b d
  bicontramap f g = (runTrans . fmap @(Flip src1_morphism) @(Transformation (Flip src2_morphism) tgt_morphism)) (Flip f) . fmap (Flip g)

type TensorProduct k = k -> k -> k
type TensorUnit k = k

type MonoidalCategory :: forall {k}. Morphism k -> TensorProduct k -> TensorUnit k -> Constraint
class ( Bifunctor morphism morphism morphism m, Category morphism) => MonoidalCategory morphism m e | morphism m -> e where -- todo: remove this functional dependency by moving rassoc and lassoc to a superclass named Semicategory
    rassoc :: (ObjectConstraint morphism a, ObjectConstraint morphism b, ObjectConstraint morphism c) => ((a `m` b) `m` c) `morphism` (a `m` (b `m` c))
    lassoc :: (ObjectConstraint morphism a, ObjectConstraint morphism b, ObjectConstraint morphism c) => (a `m` (b `m` c)) `morphism` ((a `m` b) `m` c)
    rleftunit :: ObjectConstraint morphism a => (e `m` a) `morphism` a
    lleftunit :: ObjectConstraint morphism a => a `morphism` (e `m` a)
    rrightunit :: ObjectConstraint morphism a => (a `m` e) `morphism` a
    lrightunit :: ObjectConstraint morphism a => a `morphism` (a `m` e)

type MonoidInMonoidalCategory :: forall {k}. Morphism k -> (k -> k -> k) -> k -> k -> Constraint
class (MonoidalCategory morphism m e) => MonoidInMonoidalCategory morphism m e a | a -> m morphism where
  mu :: (a `m` a) `morphism` a
  nu :: e `morphism` a

type VertComposition a b c = (b -> c) -> (a -> b) -> (a -> c)
type VertIdentity a = a -> a

-- Morphism (k -> k) denotes the category of endofunctors
-- a Monad is a monoid in the category of endofunctors where the
-- tensor product @m@ is composition and the tensor unit @e@ is identity
type Monad :: forall {k}. VertIdentity k -> VertComposition k k k -> Morphism (k -> k) -> (k -> k) -> Constraint
type Monad e m morphism a = MonoidInMonoidalCategory morphism m e a
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

type HomCategory :: forall {k}. Morphism k -> k -> k -> (k -> k) -> (k -> k) -> Type
newtype HomCategory morphism a b f g = MkHomSet (f a `morphism` g b)

class (forall a b. Category (HomCategory one_morphism a b)) => TwoCategory one_morphism two_morphism | two_morphism -> one_morphism

{-
Approach this via Bicategory instead of 2-Category?
https://stackoverflow.com/questions/25210743/bicategories-in-haskell
TODO: look at https://sjoerdvisscher.github.io/proarrow/Proarrow-Category-Bicategory.html
-}

class (MonoidalCategory two_morphism p e) => VertComp e p one_morphism two_morphism | two_morphism -> p one_morphism where
  lvertComp :: Proxy two_morphism -> (ObjectConstraint one_morphism ((p f g) a), ObjectConstraint one_morphism (f (g a))) =>  (p f g) a `one_morphism` f (g a)
  rvertComp :: Proxy two_morphism -> (ObjectConstraint one_morphism (f (g a)), ObjectConstraint one_morphism ((p f g) a)) => f (g a) `one_morphism` (p f g) a
  -- lvertComp :: Proxy two_morphism -> (p f g) a `one_morphism` f (g a)
  -- rvertComp :: Proxy two_morphism -> f (g a) `one_morphism` (p f g) a

  lvertId :: Proxy two_morphism -> (ObjectConstraint one_morphism (e a), ObjectConstraint one_morphism a) => e a `one_morphism` a
  rvertId :: Proxy two_morphism -> (ObjectConstraint one_morphism (e a), ObjectConstraint one_morphism a) => a `one_morphism` e a

  lenriched :: Proxy two_morphism -> (ObjectConstraint two_morphism f, ObjectConstraint two_morphism g) => (forall a. (ObjectConstraint one_morphism (f a), ObjectConstraint one_morphism (g a)) => f a `one_morphism` g a) -> (f `two_morphism` g)
  renriched :: Proxy two_morphism -> (ObjectConstraint two_morphism f, ObjectConstraint two_morphism g) => (f `two_morphism` g) -> (forall a. (ObjectConstraint one_morphism (f a), ObjectConstraint one_morphism (g a)) => f a `one_morphism` g a)


type StrictMonad :: forall {k}. VertIdentity k -> VertComposition k k k -> Morphism k -> Morphism (k -> k) -> (k -> k) -> Constraint
class
    ( --forall (a :: k). Coercible (e a) a
    --, forall (a :: k). Coercible ((p m m) a) (m (m a))
    --, forall (f :: k -> k) (g :: k -> k). Coercible (f `two_morphism` g) (NatCopy one_morphism f g) -- move this constraint to the definition of TwoCategory?
    --, forall (a :: k) (b :: k) (c :: k). Coercible a b => Coercible (a `one_morphism` c) (b `one_morphism` c)  -- is this constraint related to (.#) from the profunctor module? Basically this requires that one_morphism is a newtype whose first argument must not have the nominal role, see https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Coerce.html#t:Coercible
     Monad e p two_morphism m
    , Category one_morphism
    , VertComp e p one_morphism two_morphism
    -- , TwoCategory e' p' e p one_morphism two_morphism
    )
    => StrictMonad e p one_morphism two_morphism (m :: k -> k) where
  join :: forall a. (ObjectConstraint one_morphism (m (m a)), ObjectConstraint one_morphism (m a)) => (m (m a) `one_morphism` m a)
  -- join = coerce gg
  --   where
  --     gg :: (p m m) a `one_morphism` m a
  --     gg = coerce (mu @e @p @two_morphism @m)
  default join :: forall a. (ObjectConstraint one_morphism (m (m a)), ObjectConstraint one_morphism (m a), ObjectConstraint one_morphism (p m m a), ObjectConstraint two_morphism m, ObjectConstraint two_morphism (p m m)) => (m (m a) `one_morphism` m a)
  join = renriched (Proxy @two_morphism) mu . rvertComp (Proxy @two_morphism)

  returN :: forall a. (ObjectConstraint one_morphism a, ObjectConstraint one_morphism (m a)) => (a `one_morphism` m a)
  -- returN = coerce gg
  --   where
  --     gg :: e a `one_morphism` m a
  --     gg = coerce (nu @e @p @two_morphism @m)
  default returN :: forall a. (ObjectConstraint one_morphism a, ObjectConstraint one_morphism (m a), ObjectConstraint one_morphism (e a), ObjectConstraint two_morphism m, ObjectConstraint two_morphism e) => (a `one_morphism` m a)
  returN = renriched (Proxy @two_morphism) nu . rvertId (Proxy @two_morphism)

-- https://ncatlab.org/nlab/show/relative+monad#idea
type RelativeMonad :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> (i -> j) -> Constraint
class (Functor src_morphism tgt_morphism j, Functor src_morphism tgt_morphism m) => RelativeMonad src_morphism tgt_morphism j m | m tgt_morphism -> src_morphism, m -> j where
  pure :: ObjectConstraint src_morphism a => j a `tgt_morphism` m a
  (=<<) :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => (j a `tgt_morphism` m b) -> (m a `tgt_morphism` m b)


-- #########################################
-- instances for the normal function type (->)
-- #########################################

instance Category (->) where
  type ObjectConstraint (->) = Vacuous (->)
  id = Prelude.id
  (.) = (Prelude..)

type Vacuous :: Morphism i -> i -> Constraint
class Vacuous c a
instance Vacuous c a

instance Functor (->) (->) ((->) a) where
  fmap = (.)


-- #########################################
-- instances for Op, the opposite category
-- #########################################

type Op :: Morphism k -> k -> k -> Type
newtype Op morphism a b = Op (morphism b a)

deriving via (Flip (morphism :: Morphism k)) instance Category morphism => Category (Op morphism)


-- #########################################
-- instances for Flip
-- #########################################

type Flip :: (i -> j -> Type) -> j -> i -> Type
newtype Flip p a b = Flip { runFlip :: p b a }

instance Category morphism => Category (Flip morphism) where
  type ObjectConstraint (Flip morphism) = ObjectConstraint morphism
  id = Flip id
  (.) (Flip f) (Flip g) = Flip (g . f)

instance Category (Transformation (Flip (->)) (Flip (->))) where
  type ObjectConstraint (Transformation (Flip (->)) (Flip (->))) = Vacuous (Transformation (Flip (->)) (Flip (->)))
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)

-- #########################################
-- MonoidalCategory with flipped tensor product

 -- first to second
instance Functor (->) Trans p => Functor (->) (->) (Flip p a) where
  fmap f = Flip . runTrans (fmap @(->) @Trans f) . runFlip

 -- second to first
instance
    ( forall a. Functor (->) (->) (p a)
    ) => Functor (->) Trans (Flip p) where
  fmap f = Trans (Flip . fmap f . runFlip)

instance (Bifunctor (->) (->) (->) p) => Bifunctor (->) (->) (->) (Flip p) where

instance MonoidalCategory (->) m e => MonoidalCategory (->) (Flip m) e where
  rassoc = Flip . first Flip . lassoc . second runFlip . runFlip
  lassoc = Flip . second Flip . rassoc . first runFlip . runFlip
  rleftunit = rrightunit . runFlip
  lleftunit = Flip . lrightunit
  rrightunit = rleftunit . runFlip
  lrightunit = Flip . lleftunit

-- #########################################
-- MonoidalCategory instance with opposite category

instance (Functor (->) (->) (p a)) => Functor (Flip (->)) (Flip (->)) (p a) where
  fmap = Flip . fmap . runFlip

instance
    ( Functor (->) (Transformation (->) (->)) p
    )
    => Functor (Flip (->)) (Transformation (Flip (->)) (Flip (->))) p
    where
  fmap f = Trans (Flip (runTrans (fmap @(->) @Trans (runFlip f))))

instance
    ( Bifunctor (->) (->) (->) p
    )
    => Bifunctor (Flip (->)) (Flip (->)) (Flip (->)) p

instance
    ( MonoidalCategory (->) m e
    )
    => MonoidalCategory (Flip (->)) m e where
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

-- #########################################
-- instances for Flip1 Product

instance
    ( Functor (->) (->) a
    , Functor (->) (->) b
    )
    => Functor (->) (->) (Flip1 Product a b) where
  fmap f = Flip1 . fmap f . runFlip1

 -- first to second
instance Functor (->) (->) a => Functor Nat Nat (Flip1 Product a) where
  fmap f = Nat (Flip1 . runNat (runTrans (fmap @Nat @(Transformation Nat Nat) f)) . runFlip1)

 -- second to first
instance Functor Nat (Transformation Nat Nat) (Flip1 Product) where
  fmap f = Trans (Nat (Flip1 . runNat (fmap @Nat @Nat f) . runFlip1))

instance Bifunctor Nat Nat Nat (Flip1 Product)

bimapFlippedProduct
  ::
    ( ObjectConstraint Nat a
    , ObjectConstraint Nat b
    , ObjectConstraint Nat c
    , ObjectConstraint Nat d
    )
  => Nat a c
  -> Nat b d
  -> Nat
      (Flip1 Product a b)
      (Flip1 Product c d)
bimapFlippedProduct = bimap @(Type -> Type) @(Type -> Type) @(Type -> Type) @Nat @Nat @Nat @(Flip1 Product)


lassocFlipped2 = lassoc @(Flip (->)) @(Flip (,)) @()


-- #########################################
-- Profunctor instance for the normal function type (->)
-- #########################################

instance Functor (Flip (->)) Nat (->) where
  fmap f = Nat (. runFlip f)

instance Functor (Flip (->)) Trans (->) where
  fmap f = Trans (. runFlip f)

instance Bifunctor (Flip (->)) (->) (->) (->) where
  bimap f g h = g . h . runFlip f
  first f = (. runFlip f)

instance Profunctor (->) (->) (->) (->) where
  dimap f g h = g . h . f
  lmap f g = g . f


-- #########################################
-- definition of Transformation (Trans) and its Category instance
-- unlike a natural transformation a mere transformation lacks the functor constraint
-- this is probably not the best name
-- #########################################

type Trans :: Morphism (Type -> Type)
type Trans = Transformation (->) (->)

type Transformation :: forall {i} {k}. Morphism i -> Morphism k -> Morphism (i -> k)
data Transformation src_morphism tgt_morphism f g where
  Trans
    :: {- ( Category src_morphism
       , Category tgt_morphism
       , forall a. (ObjectConstraint src_morphism a) => Obj tgt_morphism (f a)
       )
    => -} { runTrans :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) }
    -> Transformation src_morphism tgt_morphism f g

instance Category Trans where
  type ObjectConstraint Trans = Vacuous Trans
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)

instance Category (Transformation Trans Trans) where
  type ObjectConstraint (Transformation Trans Trans) = Vacuous (Transformation Trans Trans)
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)


-- #########################################
-- definition of natural transformation (Nat) and its Category instance
-- #########################################

type Nat :: Morphism (Type -> Type)
type Nat = NatTrans (->) (->)

type NatTrans :: forall {i} {k}. Morphism i -> Morphism k -> Morphism (i -> k)
data NatTrans src_morphism tgt_morphism f g where
  -- Nat :: (Functor src_morphism tgt_morphism f, Functor src_morphism tgt_morphism g) => { runNat :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) } -> NatTrans src_morphism tgt_morphism f g
  Nat
    :: Functor src_morphism tgt_morphism f
    => { runNat :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) }
    -> NatTrans src_morphism tgt_morphism f g
  -- Nat :: { runNat :: forall a. ObjectConstraint morphism a => morphism (f a) (g a) } -> NatTrans morphism f g

instance (Category src_morphism, Category tgt_morphism) => Category (NatTrans (src_morphism :: Morphism i) (tgt_morphism :: Morphism k) :: Morphism (i -> k)) where
  type ObjectConstraint (NatTrans src_morphism tgt_morphism) = Functor src_morphism tgt_morphism
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)

instance Category (Transformation Nat Nat) where
  type ObjectConstraint (Transformation Nat Nat) = Functor Nat Nat
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)

instance MonoidalCategory Nat Compose Identity where
  -- in case of the assoc and rightunit conversions we need to utilize the Functor instance of the most outer functor, because the role of its type argument could be nominal
  rassoc = Nat (Compose . fmap Compose . getCompose . getCompose)
  lassoc =  Nat (Compose . Compose . fmap getCompose . getCompose)
  rleftunit = Nat (runIdentity . getCompose)
  lleftunit = Nat (Compose . Identity)
  rrightunit = Nat (fmap runIdentity . getCompose)
  lrightunit = Nat (Compose . fmap Identity)

instance VertComp Identity Compose (->) Nat where
  lvertComp _ = getCompose
  rvertComp _ = Compose
  lvertId _ = runIdentity
  rvertId _ = Identity
  lenriched _ f = Nat f
  renriched _ f = runNat f

type MonadMorphism :: Morphism (Type -> Type)
type MonadMorphism = MonadMorphism' (->)

type MonadMorphism' :: forall {i}. Morphism i -> Morphism (i -> i)
data MonadMorphism' morphism f g where
  MonadMorphism
    :: (morphism ~ (->), AuxMonad f) => { runMonadMorphism :: forall a. ObjectConstraint morphism a
    => morphism (f a) (g a) }
    -> MonadMorphism' morphism f g

instance Category MonadMorphism where
  type ObjectConstraint MonadMorphism = AuxMonad
  id = MonadMorphism id
  (.) (MonadMorphism f) (MonadMorphism g) = MonadMorphism (f . g)

instance Category (Transformation MonadMorphism Nat) where
  type ObjectConstraint (Transformation MonadMorphism Nat) = Functor MonadMorphism Nat
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)


-- #########################################
-- instances for Compose
-- #########################################

instance (Functor (->) (->) f, Functor (->) (->) g) => Functor (->) (->) (Compose f g) where
  fmap f = Compose . fmap (fmap @(->) @(->) f) . getCompose

instance Functor (->) (->) t => Functor Nat Nat (Compose t) where
  fmap (Nat f) = Nat (Compose . fmap f . getCompose)

instance Functor Nat (Transformation Nat Nat) Compose where
  fmap (Nat f) = Trans (Nat (Compose . f . getCompose))

instance Bifunctor Nat Nat Nat Compose where
  bimap (Nat f) (Nat g) = Nat (Compose . f . fmap g . getCompose)
  first (Nat f) = Nat (Compose . f . getCompose)


-- #########################################
-- instances for Identity
-- #########################################

instance Functor (->) (->) Identity where
  fmap f (Identity x) = Identity (f x)


-- #########################################
-- definition of naturals transformations between natural transformations (NatNat)
-- #########################################

type NatNat :: Morphism ((Type -> Type) -> (Type -> Type))
type NatNat = NatTrans Nat Nat

instance Category (Transformation NatNat NatNat) where
  type ObjectConstraint (Transformation NatNat NatNat) = Functor NatNat NatNat
  id = Trans id
  (.) (Trans f) (Trans g) = Trans (f . g)

fmap2 :: forall f a b. (Functor Nat Nat f, Functor (->) (->) a,  Functor (->) (->) b) => (forall x. a x -> b x) -> (forall x. f a x -> f b x)
fmap2 f = runNat (fmap @Nat @Nat @f @a @b (Nat f))

instance MonoidalCategory NatNat ComposeT IdentityT where
  rassoc = Nat (Nat (ComposeT . fmap2 ComposeT . getComposeT . getComposeT))
  lassoc = Nat (Nat (ComposeT . ComposeT . fmap2 getComposeT . getComposeT))
  rleftunit = Nat (Nat (runIdentityT . getComposeT))
  lleftunit = Nat (Nat (ComposeT . IdentityT))
  rrightunit = Nat (Nat (fmap2 runIdentityT . getComposeT))
  lrightunit = Nat (Nat (ComposeT . fmap2 IdentityT))

instance VertComp IdentityT ComposeT Nat NatNat where
  lvertComp _ = Nat getComposeT
  rvertComp _ = Nat ComposeT
  lvertId _ = Nat runIdentityT
  rvertId _ = Nat IdentityT
  lenriched _ f = Nat f
  -- renriched _ f = runNat f


-- #########################################
-- instances for ComposeT
-- #########################################

instance Functor (->) (->) (f (g a)) => Functor (->) (->) (ComposeT f g a) where
  fmap :: forall x y. (x -> y) -> ComposeT f g a x -> ComposeT f g a y
  fmap = coerce (fmap @(->) @(->) @(f (g a)) @x @y)

instance (Functor Nat Nat f, Functor Nat Nat g) => Functor Nat Nat (ComposeT f g) where
  fmap (Nat f) = Nat (\(ComposeT x) -> ComposeT (fmap2 (fmap2 f) x))

instance Functor Nat Nat z => Functor NatNat NatNat (ComposeT z) where
  fmap (Nat f) = Nat (Nat (ComposeT . fmap2 (runNat f) . getComposeT))

instance Functor NatNat (Transformation NatNat NatNat) ComposeT where
  fmap (Nat f) = Trans (Nat (Nat (ComposeT . runNat f . getComposeT)))

instance Bifunctor NatNat NatNat NatNat ComposeT where
  bimap (Nat f) (Nat g) = Nat (Nat (ComposeT . runNat f . fmap2 (runNat g) . getComposeT))
  first (Nat f) = Nat (Nat (ComposeT . runNat f . getComposeT))


-- #########################################
-- instances for IdentityT
-- #########################################

instance Functor Nat Nat IdentityT where
  fmap (Nat f) = Nat (IdentityT . f . runIdentityT)

instance Functor (->) (->) f => Functor (->) (->) (IdentityT f) where
  fmap func = coerce (fmap @(->) @(->) @f func)


-- #########################################
-- monoidal category instances for (,) in the category (->)
-- #########################################

instance Functor (->) (->) ((,) a) where
  fmap = Prelude.fmap

instance Functor (->) Trans (,) where
  fmap f = Trans (Base.Bifunctor.first f)

instance Bifunctor (->) (->) (->) (,) where
  bimap = Base.Bifunctor.bimap
  first = Base.Bifunctor.first

instance MonoidalCategory (->) (,) () where
  rassoc ((a, b), c) = (a, (b, c))
  lassoc (a, (b, c)) = ((a, b), c)
  rleftunit ((), a) = a
  lleftunit a = ((), a)
  rrightunit (a, ()) = a
  lrightunit a = (a, ())


-- #########################################
-- monoidal category instances for Either in the category (->)
-- #########################################

instance Functor (->) (->) (Either a) where
  fmap = Prelude.fmap

instance Functor (->) Trans Either where
  fmap f = Trans (Base.Bifunctor.first f)

instance Bifunctor (->) (->) (->) Either where
  bimap = Base.Bifunctor.bimap
  first = Base.Bifunctor.first

instance MonoidalCategory (->) Either Void where
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

instance (Functor (->) (->) f, Functor (->) (->) g) => Functor (->) (->) (Product f g) where
  fmap f (Pair fa ga) = Pair (fmap f fa) (fmap f ga)

instance (Functor (->) (->) a) => Functor Nat Nat (Product a) where
  fmap (Nat f) = Nat (\(Pair x y) -> Pair x (f y))

instance Functor Nat (Transformation Nat Nat) Product where
  fmap (Nat f) = Trans (Nat (\(Pair x y) -> Pair (f x) y))

instance Bifunctor Nat Nat Nat Product where
  bimap (Nat f) (Nat g) = Nat (\(Pair x y) -> Pair (f x) (g y))
  first (Nat f) = Nat (\(Pair x y) -> Pair (f x) y)

instance Functor (->) (->) Proxy where
  fmap _f Proxy = Proxy

instance MonoidalCategory Nat Product Proxy where
  rassoc = Nat (\(Pair (Pair a b) c) -> Pair a (Pair b c))
  lassoc = Nat (\(Pair a (Pair b c)) -> Pair (Pair a b) c)
  rleftunit = Nat (\(Pair Proxy a) -> a)
  lleftunit = Nat (Pair Proxy)
  rrightunit = Nat (\(Pair a Proxy) -> a)
  lrightunit = Nat (`Pair` Proxy)


-- #########################################
-- monoidal category instances for Sum in the category Nat
-- #########################################

instance (Functor (->) (->) f, Functor (->) (->) g) => Functor (->) (->) (Sum f g) where
  fmap f = \case
    InL fa -> InL (fmap f fa)
    InR ga -> InR (fmap f ga)

instance (Functor (->) (->) a) => Functor Nat Nat (Sum a) where
  fmap (Nat f) = Nat (\case
    InL ax -> InL ax
    InR bx -> InR (f bx))

instance Functor Nat (Transformation Nat Nat) Sum where
  fmap (Nat f) = Trans (Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR bx))

instance Bifunctor Nat Nat Nat Sum where
  bimap (Nat f) (Nat g) = Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR (g bx))
  first (Nat f) = Nat (\case
    InL ax -> InL (f ax)
    InR bx -> InR bx)

data Void1 a

absurd1 :: Void1 x -> b
absurd1 v = case v of {}

instance Functor (->) (->) Void1 where
  fmap _f = absurd1

instance MonoidalCategory Nat Sum Void1 where
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

instance Prelude.Monad m => Functor (->) (->) (Control.Applicative.WrappedMonad m) where
  fmap = Prelude.fmap . coerce
instance Prelude.Monad m => MonoidInMonoidalCategory Nat Compose Identity (Control.Applicative.WrappedMonad m) where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)

instance Prelude.Monad m => StrictMonad Identity Compose (->) Nat (Control.Applicative.WrappedMonad m)

instance Functor (->) (->) IO where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Nat Compose Identity IO where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Nat IO

instance Functor (->) (->) Maybe where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Nat Compose Identity Maybe where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Nat Maybe


-- #########################################
-- instances for Stream
-- #########################################

instance (Functor (->) (->) f, AuxMonad m) => Functor (->) (->) (Stream f m) where
  fmap = fmapStream

instance (Functor (->) (->) f, AuxMonad m) => MonoidInMonoidalCategory Nat Compose Identity (Stream f m) where
  mu = Nat (joinStream . getCompose)
  nu = Nat (Return . runIdentity)

instance Functor Nat (Transformation MonadMorphism Nat) Stream where
  fmap (Nat f) = Trans (Nat (maps f))

instance Functor (->) (->) f => Functor MonadMorphism Nat (Stream f) where
  fmap (MonadMorphism f) = Nat (hoistStream f)

instance Bifunctor Nat MonadMorphism Nat Stream where
  first (Nat f) = Nat (maps f)
  bimap (Nat f) (MonadMorphism g) = Nat (mapsHoistStream f g)

instance (AuxMonad m) => RelativeMonad Nat Nat IdentityT (Flip1 Stream m) where
  pure = Nat (coerce yields)
  (=<<) (Nat f) = Nat (coerce (concats @_ @m . maps @m @_ @(Stream _ m) (coerce f)))

instance (Functor (->) (->) f, AuxMonad m) => MonoidInMonoidalCategory Nat Compose Identity (Flip1 Stream m f) where
  mu = Nat (Flip1 . joinStream . fmap runFlip1 . runFlip1 . getCompose)
  nu = Nat (Flip1 . Return . runIdentity)


-- #########################################
-- instances for Flip1 Stream
-- #########################################

instance (Functor (->) (->) (Stream f m)) => Functor (->) (->) (Flip1 Stream m f) where
  fmap f = Flip1 . fmap f . runFlip1

-- first to second
instance (AuxMonad m) => Functor Nat Nat (Flip1 Stream m) where
  fmap f = Nat (Flip1 . runNat (runTrans (fmap @Nat @(Transformation MonadMorphism Nat) f)) . runFlip1)
  -- fmap f = Nat (Flip1 . maps (runNat f) . runFlip1)

instance (AuxMonad m) => MonoidInMonoidalCategory NatNat ComposeT IdentityT (Flip1 Stream m) where
  mu = Nat (Nat (coerce (concats . maps coerce)))
  nu = Nat (Nat (coerce yields))

instance (AuxMonad m) => StrictMonad IdentityT ComposeT Nat NatNat (Flip1 Stream m) where

 -- second to first
instance Functor MonadMorphism (Transformation Nat Nat) (Flip1 Stream) where
  fmap (MonadMorphism f) = Trans (Nat (Flip1 . hoistStream f . runFlip1))

instance Bifunctor MonadMorphism Nat Nat (Flip1 Stream) where
  first (MonadMorphism f) = Nat (Flip1 . hoistStream f . runFlip1)
  bimap (MonadMorphism f) (Nat g) = Nat (Flip1 . mapsHoistStream g f . runFlip1)


-- #########################################
-- definitions for AuxMonad
-- #########################################

-- temporary class that requires both Monad from Prelude as well as Functor from this module
-- will hopefully be superseeded by a Monad class defined in this module, which will require Functor from this module
class (MonoidInMonoidalCategory Nat Compose Identity m, Functor (->) (->) m) => AuxMonad m
instance (MonoidInMonoidalCategory Nat Compose Identity m, Functor (->) (->) m) => AuxMonad m

return :: forall m a. AuxMonad m => a -> m a
return x = (runNat (nu :: Nat Identity m)) (Identity x)

(>>=) :: forall m a b. AuxMonad m => m a -> (a -> m b) -> m b
(>>=) mx f = (runNat (mu :: Nat (Compose m m) m)) (Compose (fmap f mx))

(>>) :: forall m a b. AuxMonad m => m a -> m b -> m b
(>>) mx my = mx >>= \_ -> my


-- #########################################
-- definitions for Stream
-- #########################################

-- copypasted definitions that were changed to
-- require AuxMonad m instead of Prelude.Monad m
-- and Functor (->) (->) f instead of Prelude.Functor f

maps :: (AuxMonad m, Functor (->) (->) f) => (forall x. f x -> g x) -> Stream f m r -> Stream g m r
maps phi = loop where
  loop stream = case stream of
    Return r -> Return r
    Effect m -> Effect (fmap loop m)
    Step   f -> Step (phi (fmap loop f))
{-# INLINABLE maps #-}

concats :: forall f m r. (AuxMonad m, Functor (->) (->) f) => Stream (Stream f m) m r -> Stream f m r
concats = loop where
  loop :: Stream (Stream f m) m r -> Stream f m r
  loop stream = case stream of
    Return r -> Return r
    Effect m -> (Effect . fmap Return) m `bindStream` loop
    Step fs  -> fs `bindStream` loop
{-# INLINE concats #-}

bindStream :: (AuxMonad m, Functor (->) (->) f) => Stream f m t -> (t -> Stream f m r) -> Stream f m r
stream `bindStream` f =
  loop stream where
  loop stream0 = case stream0 of
    Step fstr -> Step (fmap loop fstr)
    Effect m  -> Effect (fmap loop m)
    Return r  -> f r
{-# INLINABLE bindStream #-}

joinStream :: (AuxMonad m, Functor (->) (->) f) => Stream f m (Stream f m r) -> Stream f m r
joinStream stream = bindStream stream id

yields :: (AuxMonad m, Functor (->) (->) f) => f r -> Stream f m r
yields fr = Step (fmap Return fr)
{-# INLINE yields #-}

fmapStream :: forall f m a b. (AuxMonad m, Functor (->) (->) f) => (a -> b) -> Stream f m a -> Stream f m b
fmapStream f = loop where
  loop stream = case stream of
    Return r -> Return (f r)
    Effect m -> Effect (StreamListLikeMonad.do {stream' <- m; return (loop stream')})
    Step   g -> Step (fmap loop g)
{-# INLINABLE fmapStream #-}

hoistStream :: (AuxMonad m, Functor (->) (->) f) => (forall x. m x -> n x) -> Stream f m a -> Stream f n a
hoistStream trans = loop where
  loop stream = case stream of
    Return r -> Return r
    Effect m -> Effect (trans (fmap loop m))
    Step f   -> Step (fmap loop f)
{-# INLINABLE hoistStream #-}

mapsHoistStream :: (AuxMonad m, Functor (->) (->) f) => (forall x. f x -> g x) -> (forall x. m x -> n x) -> Stream f m r -> Stream g n r
mapsHoistStream phi trans = loop where
  loop stream = case stream of
    Return r -> Return r
    Effect m -> Effect (trans (fmap loop m))
    Step g   -> Step (phi (fmap loop g))
{-# INLINABLE mapsHoistStream #-}