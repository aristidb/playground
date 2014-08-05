{-# LANGUAGE DeriveFunctor, ScopedTypeVariables, ViewPatterns #-}

module ZipStream where

import Control.Applicative
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Data.Function

data ZipStream a = ZipStream {headZ :: a, tailZ :: ZipStream a}
  deriving (Functor)

-- Just give a taste...
instance Show a => Show (ZipStream a) where
  show (ZipStream a (ZipStream b (ZipStream c _))) =
    "(" ++ show a ++ " , " ++ show b ++ " , " ++ show c ++ ")"

instance Arbitrary a => Arbitrary (ZipStream a) where
  arbitrary = sequenceA (pure arbitrary)

instance Applicative ZipStream where
  pure x = let t = ZipStream x t in t
  ZipStream f m <*> ZipStream v k = ZipStream (f v) (m <*> k)

instance Monad ZipStream where
  return = pure
  m >>= k = joinZ (fmap k m)

instance Foldable ZipStream where
  foldMap f (ZipStream a as) = f a <> foldMap f as

instance Traversable ZipStream where
  sequenceA (ZipStream m ms) = ZipStream <$> m <*> sequenceA ms

joinZ :: ZipStream (ZipStream a) -> ZipStream a
joinZ (ZipStream a x) = ZipStream (headZ a) (joinZ $ tailZ <$> x)

upFrom :: Integer -> ZipStream Integer
upFrom x = ZipStream x (upFrom (x + 1))

takeZ :: Int -> ZipStream a -> [a]
takeZ n (ZipStream a x) | n > 0    = a : takeZ (n - 1) x
                        | otherwise = []

(!!!) :: ZipStream a -> Int -> a
ZipStream a _ !!! 0 = a
ZipStream _ x !!! n = x !!! (n - 1)

previewZ :: ZipStream a -> [a]
previewZ = takeZ 20

(=?=) :: Eq a => ZipStream a -> ZipStream a -> Bool
a =?= b = previewZ a == previewZ b

infix 3 =?=

fapply :: ZipStream (Fun a b) -> ZipStream (a -> b)
fapply = fmap apply

prop_Identity v
  = pure id <*> v =?= v
prop_Composition (fapply -> u) (fapply -> v) w
  = pure (.) <*> u <*> v <*> w =?= u <*> (v <*> w)
prop_Homomorphism (apply -> f) x
  = pure f <*> pure x =?= pure (f x)
prop_Interchange (fapply -> u) y
  = u <*> pure y =?= pure ($ y) <*> u
prop_Fmap (apply -> f) x
  = fmap f x =?= pure f <*> x

prop_Applicative :: forall a b c. (Eq a, Eq b, Eq c,
                                   Show a, Show b, Show c,
                                   Arbitrary a, Arbitrary b, Arbitrary c,
                                   CoArbitrary a, CoArbitrary b, CoArbitrary c,
                                   Function a, Function b) =>
                    a -> b -> c -> Property
prop_Applicative _ _ _ = (prop_Identity :: ZipStream a -> Bool) .&.
                         (prop_Composition :: ZipStream (Fun b c) -> ZipStream (Fun a b) -> ZipStream a -> Bool) .&.
                         (prop_Homomorphism :: Fun a b -> a -> Bool) .&.
                         (prop_Interchange :: ZipStream (Fun a b) -> a -> Bool) .&.
                         (prop_Fmap :: Fun a b -> ZipStream a -> Bool)
