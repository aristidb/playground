{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module FingerMap where

import Data.FingerTree (FingerTree, Measured(..))
import qualified Data.FingerTree as FT
import Data.Monoid
import Prelude hiding (lookup, splitAt, length)

{-
instance (Measured v b) => Measured v (a, b) where
    measure (_, b) = measure b
-}

data Node a = Elem {-# UNPACK #-} !Int a
    deriving (Show)

instance Measured (Sum Int) (Node a) where
    measure (Elem n _) = Sum n

newtype FingerMap a = FM (FingerTree (Sum Int) (Node a))
    deriving (Show)

unFM :: FingerMap a -> FingerTree (Sum Int) (Node a)
unFM (FM a) = a

instance Measured (Sum Int) (FingerMap a) where
    measure (FM a) = measure a

singleton :: a -> FingerMap a
singleton a = FM (FT.singleton (Elem 1 a))
{-# INLINE singleton #-}

fromElemList :: [a] -> FingerMap a
fromElemList xs = FM (FT.fromList (map (Elem 1) xs))

instance Monoid (FingerMap a) where
    mempty = FM FT.empty
    mappend (FM x) (FM y) = FM (x <> y)

length :: FingerMap a -> Int
length x = getSum (measure x)

lookup :: FingerMap a -> Int -> FingerMap a
lookup (FM x) i | measure a < Sum i = mempty
                | otherwise = case FT.viewr a of
                                FT.EmptyR -> mempty
                                _ FT.:> e -> FM (e FT.<| FT.dropUntil (> Sum 0) b)
  where
    (a, b) = FT.split (> Sum i) x

{-
splitAt :: Int -> FingerMap a -> (FingerMap a, FingerMap a)
splitAt i (FM x) =
    case FT.viewl b of
      FT.EmptyL -> (FM a, mempty)
      Filler n FT.:< b' -> (FM a <> filler (i - c), filler (c + n - i) <> FM b')
      Elem _ FT.:< _ -> (FM a, FM b)
  where
    (a, b) = FT.split (> Sum i) x
    Sum c = measure a

update :: Int -> (Maybe a -> Maybe a) -> FingerMap a -> FingerMap a
update i f x =
    case (e, f e) of
      (Nothing, Nothing) -> x
      (Just _, Nothing) -> a <> filler 1 <> b'
      (_, Just e') -> a <> filler (i - c) <> singleton e' <> b'
  where
    (a, b) = splitAt i x
    Sum c = measure a
    (e, b') = case FT.viewl (unFM b) of
          FT.EmptyL -> (Nothing, mempty)
          Filler n FT.:< q -> (Nothing, filler (n - 1) <> FM q)
          Elem p FT.:< q -> (Just p, FM q)
-}
