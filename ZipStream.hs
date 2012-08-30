{-# LANGUAGE DeriveFunctor #-}

module ZipStream where

import Control.Applicative

data ZipStream a = ZipStream {headZ :: a, tailZ :: ZipStream a}
  deriving (Functor)

-- Just give a taste...
instance Show a => Show (ZipStream a) where
  show (ZipStream a (ZipStream b (ZipStream c _))) = "(" ++ show a ++ " , " ++ show b ++ " , " ++ show c ++ ")"

instance Applicative ZipStream where
  pure x = let t = ZipStream x t in t
  ZipStream f m <*> ZipStream v k = ZipStream (f v) (m <*> k)

instance Monad ZipStream where
  return = pure
  m >>= k = joinZ (fmap k m)

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
