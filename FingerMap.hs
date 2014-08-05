{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module FingerMap where

import Data.FingerTree (FingerTree, Measured(..))
import qualified Data.FingerTree as FT
import Data.Monoid
import Prelude hiding (splitAt, length)

data Node a = Elem a | Filler {-# UNPACK #-} !Int
    deriving (Show)

instance Measured (Sum Int) (Node a) where
    measure (Elem _) = Sum 1
    measure (Filler n) = Sum n

newtype FingerMap a = FM (FingerTree (Sum Int) (Node a))
    deriving (Show)

unFM :: FingerMap a -> FingerTree (Sum Int) (Node a)
unFM (FM a) = a

instance Measured (Sum Int) (FingerMap a) where
    measure (FM a) = measure a

singleton :: a -> FingerMap a
singleton a = FM (FT.singleton (Elem a))
{-# INLINE singleton #-}

fromElemList :: [a] -> FingerMap a
fromElemList xs = FM (FT.fromList (map Elem xs))

instance Monoid (FingerMap a) where
    mempty = FM FT.empty
    mappend a@(FM x) b@(FM y) = app (FT.viewr x) (FT.viewl y)
      where
        app FT.EmptyR _ = b
        app _ FT.EmptyL = a
        app (_ FT.:> Elem _) _ = FM (x <> y)
        app _ (Elem _ FT.:< _) = FM (x <> y)
        app (x' FT.:> Filler n) (Filler m FT.:< y') = FM $ x' <> (Filler (n + m) FT.<| y')

filler :: Int -> FingerMap a
filler 0 = mempty
filler n = FM $ FT.singleton (Filler n)

length :: FingerMap a -> Int
length x = getSum (measure x)

lookup :: FingerMap a -> Int -> Maybe a
lookup (FM x) i =
    case FT.viewl $ FT.dropUntil (> Sum i) x of
      FT.EmptyL -> Nothing
      Filler _ FT.:< _ -> Nothing
      Elem a FT.:< _ -> Just a

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
