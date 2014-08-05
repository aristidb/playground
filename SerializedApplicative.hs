{-# LANGUAGE ViewPatterns #-}
module SerializedApplicative where

import Control.Applicative

class Choice f where
  choice :: f a -> f a -> f a

data S f a = Final (f a)
           | Intermediate { falsish :: S f a
                          , truish :: S f a }

stepS :: Bool -> S f a -> S f a
stepS v (Final x) = Final x
stepS v (Intermediate x y) = if v then x else y

execS :: S f a -> [Bool] -> Maybe (f a)
execS = undefined

split :: S f a -> (S f a, S f a)
split (Final x) = (Final x, Final x)
split (Intermediate x y) = (x, y)

instance Functor f => Functor (S f) where
  fmap f (Final x) = Final (fmap f x)
  fmap f (Intermediate x y) = Intermediate (fmap f x) (fmap f y)

instance Applicative f => Applicative (S f) where
  pure x = Final (pure x)

  Final m <*> Final x = Final (m <*> x)
  (split -> (m1, m2)) <*> (split -> (x1, x2)) = Intermediate (m1 <*> x1) (m2 <*> x2)

instance Alternative f => Alternative (S f) where
  empty = Final empty

  Final x <|> Final y = Final (x <|> y)
  (split -> (x1, x2)) <|> (split -> (y1, y2)) = Intermediate (x1 <|> y1) (x2 <|> y2)

instance Choice (S f) where
  choice a b = Intermediate a b

{-
instance Alternative f => Conditional (S f) where
  guardA 
-}

{-
data S f a = S { value :: Maybe (S f a) -> Maybe (S f a) -> f a
               , falsish :: Maybe (S f a)
               , truish :: Maybe (S f a) }

instance Functor f => Functor (S f) where
  fmap f (S a x y) = S (\x y -> fmap f (a x y))
                       (fmap (fmap f) x)
                       (fmap (fmap f) y)

instance Applicative f => Applicative (S f) where
  pure x = S (pure x) Nothing Nothing
  S f tf ff <*> S x tx fx = S (f <*> x) (go tf tx) (go ff fx)
    where go (Just g) (Just y) = Just (g <*> y)
          go _        _        = Nothing

instance Monad m => Conditional (S m) where
  ifA c a b = S undefined undefined undefined
-}
