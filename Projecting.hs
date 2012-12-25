{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Projecting where

import Control.Applicative
import Unsafe.Coerce
import Control.Category
import Control.Monad.Reader
import Control.Lens.Classes
import Control.Lens.Getter
import GHC.Prim
import Prelude hiding (id,(.))

type family A x :: *
type instance A (a -> f_b) = a
type family F x :: * -> *
type instance F (a -> f b) = f
type family B x :: *
type instance B (a -> f b) = b

type As g x = A x -> g (B x)

data From (p :: (* -> *) -> Constraint)
          (q :: (* -> *) -> Constraint) = From

type Projection = From Applicative Gettable
type Embedding = From Gettable Applicative
type Iso       = From Functor Functor

projection :: From Applicative Gettable
projection = From

embedding :: From Gettable Applicative
embedding = From

isomorphism :: From Functor Functor
isomorphism = From

class Forge (k :: * -> * -> *) (p :: (* -> *) -> Constraint) (q :: (* -> *) -> Constraint) where
  forge :: p h => From p q
               -> (forall f. p f => (a -> f b) -> s -> f t)
               -> (forall g. q g => (s -> g t) -> a -> g b)
               -> k (a -> h b) (s -> h t)

instance Forge (->) p q where
  forge _ k _ afb s = k afb s

data Forged (p :: (* -> *) -> Constraint)
            (q :: (* -> *) -> Constraint)
            x
            y where
  Forged :: (forall f. p f => (a -> f b) -> s -> f t)
         -> (forall g. q g => (s -> g t) -> a -> g b)
         -> Forged p q (a -> h b) (s -> h t)

from :: forall k p q g x y. (Forge k q p, q g) => Forged p q x y -> k (As g y) (As g x)
from (Forged l r) = forge (From :: From q p) r l

via :: forall k p q g x y. (Forge k p q, p g) => Forged p q x y -> k (As g x) (As g y)
via (Forged l r) = forge (From :: From p q) l r

instance Forge (Forged p q) p q where
  forge _ = Forged

isos :: (Forge k Functor Functor, Functor f) => (s -> a) -> (a -> s) -> (t -> b) -> (b -> t) -> k (a -> f b) (s -> f t)
isos sa as tb bt = forge (From :: From Functor Functor) (\afb s -> bt <$> afb (sa s)) (\sft a -> tb <$> sft (as a))

project :: (Forge k Applicative Gettable, Applicative f) => (a -> s) -> (forall g. Applicative g => (a -> g b) -> s -> g t) -> k (a -> f b) (s -> f t)
project as k = forge (From :: From Applicative Gettable) k (\sft -> coerce . sft . as)

embed :: (Forge k Gettable Applicative, Gettable f) => (s -> a) -> (forall g. Applicative g => (s -> g t) -> a -> g b) -> k (a -> f b) (s -> f t)
embed as k = forge (From :: From Gettable Applicative) (\sft -> coerce . sft . as) k

trans :: Forged p q (s -> f t) (x -> f y) -> Forged p q (a -> f b) (s -> f t) -> Forged p q (a -> f b) (x -> f y)
trans (Forged yz zy) (Forged xy yx) = undefined
-- trans (Forged yz zy) (Forged xy yx) = Forged (\x -> yz (xy x)) (\z -> yx (zy z))