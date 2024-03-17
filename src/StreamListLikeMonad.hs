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

module StreamListLikeMonad where
import Prelude (IO, putStrLn, undefined)
import Prelude qualified
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

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- -- type family MorphObj morphism a where
-- --   MorphObj Morph (a :: k) = k

-- -- type MorphObj2 b (a :: k) = k

-- -- type Morph :: ObjectKind4 morph (MapToKind k) -> ObjectKind4 morph (MapToKind k) -> Type
-- -- data Morph a b where
--   -- A :: forall (a :: Type) (b :: Type). (a -> b) -> Morph a b
--   -- B :: forall (a :: Constraint) (b :: Type). (a => b) -> Morph a b

-- -- type Morph2 :: forall k k -> (Type) -> (MapToKind k2) -> Type
-- type Morph2 :: forall k1 k2 -> k1 -> k2 -> Type
-- -- type Morph2 :: forall (MapToKind k1) (MapToKind k2) -> (MapToKind k1) -> (MapToKind k2) -> Type
-- data Morph2 k1 k2 (a :: k1) (b :: k2) where
--   A :: forall (a :: MapToKind Kind1) (b :: MapToKind Kind1). (a -> b) -> Morph2 (MapToKind Kind1) (MapToKind Kind1) a b
--   B :: forall (a :: MapToKind Kind2) (b :: MapToKind Kind1). (a => b) -> Morph2 (MapToKind Kind2) (MapToKind Kind1) a b


-- instance CategoryK (MapToKind k) Morph2 where
  
-- -- data Morph2 k1 k2 (a :: k1) (b :: k2) where
-- --   A :: forall (a :: Type) (b :: Type). (a -> b) -> Morph2 (Type) (Type) a b
-- --   B :: forall (a :: Constraint) (b :: Type). (a => b) -> Morph2 (Constraint) (Type) a b


-- data KindT = Kind1 | Kind2

-- type MapToKind :: KindT -> Type
-- type family MapToKind a where
--   MapToKind Kind1 = Type
--   MapToKind Kind2 = Constraint
 
 
-- #########################################
-- definition of the classes Category, Functor and RelativeMonad
-- #########################################
 
type Morphism object_kind = object_kind -> object_kind -> Type

type ObjectKind2 (morphism :: Morphism k) = k
 
type CategoryK :: forall k -> Morphism k -> Constraint
class CategoryK k (morphism :: Morphism k) | morphism -> k where
 
type Category :: forall {k}. Morphism k -> Constraint
class (k ~ ObjectKind morphism, CategoryK k morphism) => Category (morphism :: Morphism k) where
  type ObjectKind morphism :: Type
  type ObjectKind (morphism :: Morphism k) = k
  type ObjectKind4 morphism (a :: k) :: Type
  type ObjectKind4 (morphism :: Morphism k) a = k

  type ObjectConstraint morphism :: k -> Constraint
  id :: ObjectConstraint morphism a => a `morphism` a
  (.) :: (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)
-- instance  (k ~ ObjectKind morphism, CategoryK k morphism) => Category morphism

-- type Category' :: Morphism (ObjectKind )
-- class Category morphism
 
type TensorProduct k = k -> k -> k
type TensorUnit k = k

type MonoidalCategory :: forall {k}. TensorUnit k -> TensorProduct k -> Morphism k -> Constraint
class ({-Bi FunctorOf morphism m,-} Category morphism) => MonoidalCategory e m morphism | morphism -> e, morphism -> m where
    rassoc :: (ObjectConstraint morphism a, ObjectConstraint morphism b, ObjectConstraint morphism c) => ((a `m` b) `m` c) `morphism` (a `m` (b `m` c))
    lassoc :: (ObjectConstraint morphism a, ObjectConstraint morphism b, ObjectConstraint morphism c) => (a `m` (b `m` c)) `morphism` ((a `m` b) `m` c)
    rleftunit :: ObjectConstraint morphism a => (e `m` a) `morphism` a
    lleftunit :: ObjectConstraint morphism a => a `morphism` (e `m` a)
    rrightunit :: ObjectConstraint morphism a => (a `m` e) `morphism` a
    lrightunit :: ObjectConstraint morphism a => a `morphism` (a `m` e)
    
type MonoidInMonoidalCategory :: forall {k}. k -> (k -> k -> k) -> Morphism k -> k -> Constraint
class (MonoidalCategory e m morphism) => MonoidInMonoidalCategory e m morphism a | a -> morphism where
  mu :: (a `m` a) `morphism` a
  nu :: e `morphism` a

type VertComposition a b c = (b -> c) -> (a -> b) -> (a -> c)
type VertIdentity a = a -> a

-- Morphism (k -> k) denotes the category of endofunctors
-- a Monad is a monoid in the category of endofunctors where the 
-- tensor product @m@ is composition and the tensor unit @e@ is identity
type Monad :: forall {k}. VertIdentity k -> VertComposition k k k -> Morphism (k -> k) -> (k -> k) -> Constraint
type Monad e m morphism a = MonoidInMonoidalCategory e m morphism a
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



-- type TwoCategoryProper :: (zero_cell -> zero_cell -> Morphism one_cell) -> Constraint
-- class (forall (x :: zero_cell) (y :: zero_cell). Category (two_cat x y)) => TwoCategoryProper (two_cat :: (zero_cell -> zero_cell -> Morphism one_cell)) where
--   vert_id :: forall (x :: zero_cell) (y :: zero_cell) (a :: one_cell). ObjectConstraint (two_cat x y) a => two_cat x y a a
--   vert_id = id @(two_cat x y)

--   (.|) :: forall (x :: zero_cell) (y :: zero_cell) (a :: one_cell) (b :: one_cell) (c :: one_cell). two_cat x y b c -> two_cat x y a b -> two_cat x y a c
--   (.|) = (.)



--   -- MonoidalCategory e p (two_cat x y)

-- -- type TwoCategoryProper :: (zero_cell -> zero_cell -> Morphism one_cell) -> Constraint
-- class (forall (x :: zero_cell) (y :: zero_cell). Category (two_cat x y), Morphism one_cell ~ two_cell) => TwoCategoryProper (two_cat :: (zero_cell -> zero_cell -> Morphism one_cell)) (e :: two_cell) (p :: two_cell -> two_cell -> two_cell) | two_cat -> e, two_cat -> p where
--   vertId :: forall (x :: zero_cell) (y :: zero_cell) (a :: one_cell). ObjectConstraint (two_cat x y) a => two_cat x y a a
--   vertId = id @(two_cat x y)

--   verticalComposition :: forall (x :: zero_cell) (y :: zero_cell) (a :: one_cell) (b :: one_cell) (c :: one_cell). two_cat x y b c -> two_cat x y a b -> two_cat x y a c
--   verticalComposition = (.)

--   -- horizontalId ::
--   horizontalComposition :: forall (x :: zero_cell) (y :: zero_cell) (z :: zero_cell) (a :: one_cell) (b :: one_cell) (c :: one_cell). two_cat y z b c -> two_cat x y a b -> two_cat x z a c



-- verticalComposition'
--   :: forall two_cat e p x y a b c morphism.
--   ( TwoCategoryProper two_cat e p
--   , two_cat x y ~ morphism)
--   =>  (b `morphism` c) -> (a `morphism` b) -> (a `morphism` c)
-- verticalComposition' = verticalComposition

-- horizontalComposition'
--   :: forall two_cat e p x y z a b c morphism_x_y morphism_y_z morphism_x_z.
--   ( TwoCategoryProper two_cat e p
--   , two_cat x y ~ morphism_x_y
--   , two_cat y z ~ morphism_y_z
--   , two_cat x z ~ morphism_x_z)
--   => (b `morphism_y_z` c) -> (a `morphism_x_y` b) -> (a `morphism_x_z` c)
-- horizontalComposition' = horizontalComposition

--   -- https://stackoverflow.com/questions/25210743/bicategories-in-haskell
--   -- (.-) :: two_cat g g' d e -> two_cat f f' c d -> two_cat (g `p` f) (g' `p` f') c e
--   -- (.-) = mu

--   -- mu :: (a `m` a) `morphism` a
--   -- nu :: e `morphism` a

-- -- (.|) = verticalComposition
-- -- (._) = horizontalComposition

-- -- instance TwoCategoryProper Nat Identity Compose where

-- type TwoCategoryProper :: Morphism k -> k -> (k -> k -> k) -> Constraint
-- class (Functor TerminalCategory two_cat e {- Functor ProdCat two_cat comp -}) => TwoCategoryProper (two_cat :: Morphism (zero_cell -> zero_cell)) e comp | two_cat -> e, two_cat -> comp where

type TwoCategoryProper :: ( forall i k. Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type) -> idk -> (forall i j k. (j -> k) -> (i -> j) -> (i -> k)) -> Constraint
class (forall {i} {k} (c :: Morphism i) (d :: Morphism k). Category (two_cat c d)) => TwoCategoryProper (two_cat :: forall i k. Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type) el (comp :: forall i j k. (j -> k) -> (i -> j) -> (i -> k)) | two_cat -> el, two_cat -> comp where
  -- type HomCat two_cat :: forall i k -> Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type
  -- type HomCat two_cat i k = two_cat

  -- type OneCat :: Morphism i -> Morphism k ->

  id1   :: two_cat c d f f
  (.|)  :: two_cat c d g h -> two_cat c d f g -> two_cat c d f h
  (.-)  :: forall {i} {j} {k} (c :: Morphism i) (d :: Morphism j) (e :: Morphism k) (g :: j -> k) (g' :: j -> k) (f :: i -> j) (f' :: i -> j). two_cat d e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')
  -- (.-)  :: two_cat d e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')
  -- (.-)  :: forall {i} {j} {k} (c :: Morphism i) (d :: Morphism j) (e :: Morphism k) (g :: j -> k) (g' :: j -> k) (f :: i -> j) (f' :: i -> j). two_cat (HomCat ) e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')

class TwoCat (one_cat :: Morphism k) where
  -- type HomCat
  id11 :: f a `one_cat` f a
  (.||) :: (forall a. g a `one_cat` h a) -> (forall a. f a `one_cat` g a) -> (forall a. f a `one_cat` h a)
  -- (.||) :: forall {j} (f :: j -> k) (g :: j -> k) (h :: j -> k). (forall a. g a `one_cat` h a) -> (forall a. f a `one_cat` g a) -> (forall a. f a `one_cat` h a)

  (.--)  :: forall {i} {j} (c :: Morphism j) (g :: j -> k) (g' :: j -> k) (f :: i -> j) (f' :: i -> j). (forall (a :: j). g a `one_cat` g' a) -> (forall (a :: i). f a `c` f' a) -> (forall (a :: i). g (f a) `one_cat` g' (f' a))
  -- (.--)  :: (forall a. g a `one_cat` g' a) -> (forall a. f a `c` f' a) -> (forall a. g (f a) `one_cat` g' (f' a))



type HomCategory :: forall {k}. Morphism k -> k -> k -> (k -> k) -> (k -> k) -> Type
newtype HomCategory morphism a b f g = MkHomSet (f a `morphism` g b)

class (forall a b. Category (HomCategory one_morphism a b)) => TwoCategory one_morphism two_morphism | two_morphism -> one_morphism




-- type TwoCateg :: (forall {i} {k}. Morphism (Src two_cat i) -> Morphism (Tgt two_cat k) -> (Src two_cat i -> Tgt two_cat k) -> (Src two_cat i -> Tgt two_cat k) -> Type) -> (forall {i} {k}. (Src two_cat i -> Tgt two_cat k) -> (Src two_cat i -> Tgt two_cat k)) -> (forall {i} {j} {k}. (Src two_cat j -> Tgt two_cat k) -> (Src two_cat i -> Tgt two_cat j) -> (Src two_cat i -> Tgt two_cat k)) -> Constraint
type TwoCateg :: (forall {i} {k}. Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type) -> (forall {i} {k}. (i -> k) -> (i -> k)) -> (forall {i} {j} {k}. (j -> k) -> (i -> j) -> (i -> k)) -> Constraint
-- class (forall {i} {k} (c :: Morphism i) (d :: Morphism k). Category (two_cat c d)) => TwoCateg (two_cat :: forall i k. Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type) el (comp :: forall i j k. (j -> k) -> (i -> j) -> (i -> k)) | two_cat -> el, two_cat -> comp where

class (forall {i} {k} (c :: Morphism i) (d :: Morphism k). Category (two_cat c d)) => TwoCateg (two_cat) el (comp) | two_cat -> el, two_cat -> comp where
  -- type HomCat two_cat :: forall i k -> Morphism i -> Morphism k -> (i -> k) -> (i -> k) -> Type
  -- type HomCat two_cat i k = two_cat

  -- type OneCat :: Morphism i -> Morphism k ->


  id111   :: two_cat c d f f
  (.|||)  :: two_cat c d g h -> two_cat c d f g -> two_cat c d f h
  (.---)  :: forall {i} {j} {k} (c :: Morphism i) (d :: Morphism j) (e :: Morphism k) (g :: j -> k) (g' :: j -> k) (f :: i -> j) (f' :: i -> j). two_cat d e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')



type ObjectKind3 (c :: Morphism i) (d :: Morphism j) = i -> j

-- TODO: enable quantified Category superclass constraint as well as quantified signatures by adding an  associated type family "ObjectKind" to the definition of the Category typeclass and use ObjectKind everywhere.
type TwoCategg :: ( forall i k. Morphism i -> Morphism k -> Morphism (i -> k)) -> (forall i k. (i -> k) -> (i -> k)) -> (forall i j k. (j -> k) -> (i -> j) -> (i -> k)) -> Constraint
-- type TwoCategg 
--   :: (forall c d. Morphism (ObjectKind2 c) -> Morphism (ObjectKind2 d) -> Morphism (ObjectKind2 c -> ObjectKind2 d)) 
--   -> (forall c d. (ObjectKind2 c -> ObjectKind2 d) -> (ObjectKind2 c -> ObjectKind2 d))
--   -> (forall c d e. (ObjectKind2 d -> ObjectKind2 e) -> (ObjectKind2 c -> ObjectKind2 d) -> (ObjectKind2 c -> ObjectKind2 e)) 
--   -> Constraint
-- type TwoCategg
--   ::  forall 
--   -> (forall c d. (ObjectKind2 c -> ObjectKind2 d) -> (ObjectKind2 c -> ObjectKind2 d))
--   -> (forall c d e. (ObjectKind2 d -> ObjectKind2 e) -> (ObjectKind2 c -> ObjectKind2 d) -> (ObjectKind2 c -> ObjectKind2 e)) 
--   -> Constraint
class {- (forall {i} {k} (c :: Morphism i) (d :: Morphism k). ((Category c, Category d, and two_cat c d is a valid type) => Category (two_cat c d))) => -} TwoCategg two_cat el (comp) | two_cat -> el, two_cat -> comp where
  type MorphismKind two_cat c :: Type
  id1111   :: two_cat c d f f
  (.||||)  :: two_cat c d g h -> two_cat c d f g -> two_cat c d f h
  --(.----)  :: forall {i} {j} {k} (c :: Morphism i) (d :: Morphism j) (e :: Morphism k) (g :: j -> k) (g' :: j -> k) (f :: i -> j) (f' :: i -> j). two_cat d e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')

  (.----)  :: two_cat d e g g' -> two_cat c d f f' -> two_cat c e (comp g f) (comp g' f')
  -- type Object2Constraint two_cat :: Morphism i -> 
    
    -- Object2Constraint two_cat ~


-- (.----) :: NatTrans (->) (Kleisli Maybe)

instance TwoCategg 
  (NatTrans :: Morphism i -> Morphism k -> Morphism (i -> k))
  (IdentityT :: (Type -> Type) -> (Type -> Type))
  (ComposeT :: ((Type -> Type) -> (Type -> Type)) ->  ((Type -> Type) -> (Type -> Type)) ->  ((Type -> Type) -> (Type -> Type)))

-- instance TwoCategg 
--   (NatTrans :: Morphism (Type -> Type) -> Morphism (Type -> Type) -> ((Type -> Type) -> (Type -> Type)) -> ((Type -> Type) -> (Type -> Type)) -> Type)
--   (IdentityT :: (Type -> Type) -> (Type -> Type))
--   (ComposeT :: ((Type -> Type) -> (Type -> Type)) ->  ((Type -> Type) -> (Type -> Type)) ->  ((Type -> Type) -> (Type -> Type)))
--   where
--   id1111 = undefined -- Nat id
--   -- (.||||) = (.)
--   (.||||) (Nat f) (Nat g) = Nat (f . g)
--   (.----) :: forall c d e g g' f f'. NatTrans d e g g' -> NatTrans c d f f' -> NatTrans c e (ComposeT g f) (ComposeT g' f')
--   (.----) (Nat f) (Nat g) = undefined -- Nat (ComposeT . fff . getComposeT)
--     -- where
--     --   fff :: forall a i. g (f a) i -> g' (f' a) i
--     --   fff = undefined

-- instance TwoCategg NatTrans Identity Compose



class (MonoidalCategory e p two_morphism) => VertComp e p one_morphism two_morphism | two_morphism -> one_morphism where
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



type Functor :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> Constraint
class
    ( Category src_morphism
    , Category tgt_morphism
    -- , forall a. ObjectConstraint src_morphism a => ObjectConstraint tgt_morphism (f a)
    -- the line above does not work, see https://gitlab.haskell.org/ghc/ghc/-/issues/16123 , instead we use a workaround in the line below:
    , forall objConstr a. (objConstr ~ ObjectConstraint tgt_morphism, ObjectConstraint src_morphism a) => objConstr (f a)
    ) 
    => Functor (src_morphism) tgt_morphism f | f -> src_morphism tgt_morphism where
  fmap :: (ObjectConstraint src_morphism a) => (a `src_morphism` b) -> (f a `tgt_morphism` f b)
 
 
-- https://ncatlab.org/nlab/show/relative+monad#idea
type RelativeMonad :: forall {i} {j}. Morphism i -> Morphism j -> (i -> j) -> (i -> j) -> Constraint
class (Functor src_morphism tgt_morphism j, Functor src_morphism tgt_morphism m) => RelativeMonad src_morphism tgt_morphism j m | m -> j where
  pure :: ObjectConstraint src_morphism a => j a `tgt_morphism` m a
  (=<<) :: (ObjectConstraint src_morphism a, ObjectConstraint src_morphism b) => (j a `tgt_morphism` m b) -> (m a `tgt_morphism` m b)
 
  
-- #########################################
-- definition of the category instance for the normal function type (->)
-- #########################################
 
instance CategoryK Type (->) where
instance Category (->) where
  type ObjectConstraint (->) = Vacuous (->)
  id = Prelude.id
  (.) = (Prelude..)
 
type Vacuous :: Morphism i -> i -> Constraint
class Vacuous c a
instance Vacuous c a
 
 
-- #########################################
-- definition of natural transformation (Nat) and its Category instance
-- #########################################
 

type Nat :: Morphism (Type -> Type)
type Nat = NatTrans (->) (->)

type NatNat :: Morphism ((Type -> Type) -> (Type -> Type))
type NatNat = NatTrans Nat Nat

type NatTrans :: forall {i} {k}. Morphism i -> Morphism k -> Morphism (i -> k)
data NatTrans src_morphism tgt_morphism f g where
  -- Nat :: (Functor src_morphism tgt_morphism f, Functor src_morphism tgt_morphism g) => { runNat :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) } -> NatTrans src_morphism tgt_morphism f g
  Nat :: Functor src_morphism tgt_morphism f => { runNat :: forall a. ObjectConstraint src_morphism a => tgt_morphism (f a) (g a) } -> NatTrans src_morphism tgt_morphism f g
  -- Nat :: { runNat :: forall a. ObjectConstraint morphism a => morphism (f a) (g a) } -> NatTrans morphism f g

instance (Category src_morphism, Category tgt_morphism) => CategoryK (i -> k) (NatTrans (src_morphism :: Morphism i) (tgt_morphism :: Morphism k) :: Morphism (i -> k)) where
instance (Category src_morphism, Category tgt_morphism) => Category (NatTrans (src_morphism :: Morphism i) (tgt_morphism :: Morphism k) :: Morphism (i -> k)) where
  type ObjectConstraint (NatTrans src_morphism tgt_morphism) = Functor src_morphism tgt_morphism
  id = Nat id
  (.) (Nat f) (Nat g) = Nat (f . g)

instance Functor (->) (->) Identity where
  fmap f (Identity x) = Identity (f x)

instance (Functor (->) (->) f, Functor (->) (->) g) => Functor (->) (->) (Compose f g) where
  fmap f (Compose x) = Compose (fmap (fmap f) x)

instance MonoidalCategory Identity Compose Nat where
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

-- #########################################
-- definition of transformations of natural transformation (NatNat) and its Category instance
-- #########################################
 
fmap2 :: forall f a b. (Functor Nat Nat f, Functor (->) (->) a) => (forall x. a x -> b x) -> (forall x. f a x -> f b x)
fmap2 f = runNat (fmap @Nat @Nat @f @a @b (Nat f))

instance MonoidalCategory IdentityT ComposeT NatNat where
  rassoc = Nat (Nat (ComposeT . fmap2 ComposeT . getComposeT . getComposeT))
  lassoc = Nat (Nat (ComposeT . ComposeT . fmap2 getComposeT . getComposeT))
  rleftunit :: ObjectConstraint NatNat a => NatNat (ComposeT IdentityT a) a
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


-- #########################################
-- instances for IdentityT
-- #########################################
 
instance Functor Nat Nat IdentityT where
  fmap :: forall a b. Nat a b -> Nat (IdentityT a) (IdentityT b)
  fmap (Nat f) = Nat (IdentityT . f . runIdentityT :: forall x. IdentityT a x -> IdentityT b x)
 
instance Functor (->) (->) f => Functor (->) (->) (IdentityT f) where
  fmap func = coerce (fmap @(->) @(->) @f func)
  



-- #########################################
-- instances for familiar Monads such as Maybe or IO
-- #########################################

instance Prelude.Monad m => Functor (->) (->) (Control.Applicative.WrappedMonad m) where
  fmap = Prelude.fmap . coerce
instance Prelude.Monad m => MonoidInMonoidalCategory Identity Compose Nat (Control.Applicative.WrappedMonad m) where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)

instance Prelude.Monad m => StrictMonad Identity Compose (->) Nat (Control.Applicative.WrappedMonad m)

instance Functor (->) (->) IO where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Identity Compose Nat IO where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Nat IO

instance Functor (->) (->) Maybe where
  fmap = Prelude.fmap . coerce
instance MonoidInMonoidalCategory Identity Compose Nat Maybe where
  mu = Nat (Control.Monad.join . coerce)
  nu = Nat (Prelude.return . coerce)
instance StrictMonad Identity Compose (->) Nat Maybe

 
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

instance (Functor (->) (->) f, Prelude.Monad m) => MonoidInMonoidalCategory Identity Compose Nat (StreamFlip m f) where
  mu = Nat (MkStreamFlip . joinStream . fmap getStream . getStream . getCompose)
  nu = Nat (MkStreamFlip . Return . runIdentity)

instance (Prelude.Monad m) => MonoidInMonoidalCategory IdentityT ComposeT NatNat (StreamFlip m) where
  mu = Nat (Nat (coerce (concats . maps coerce)))
  nu = Nat (Nat (coerce yields))

instance (Prelude.Monad m) => StrictMonad IdentityT ComposeT Nat NatNat (StreamFlip m) where

-- #########################################
-- definitions for Stream
-- #########################################
 
 
-- Functor instance
 
instance (Functor (->) (->) f, Prelude.Monad m) => Functor (->) (->) (Stream f m) where
  fmap f = loop where
    loop stream = case stream of
      Return r -> Return (f r)
      Effect m -> Effect (do {stream' <- m; Prelude.return (loop stream')})
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

joinStream :: (Prelude.Monad m, Functor (->) (->) f) => Stream f m (Stream f m r) -> Stream f m r
joinStream stream = bindStream stream id
 
yields :: (Prelude.Monad m, Functor (->) (->) f) => f r -> Stream f m r
yields fr = Step (fmap Return fr)
{-# INLINE yields #-}