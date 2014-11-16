module ThingTree where

-- import Test.QuickCheck
import Data.List (sort, sortBy)
import Data.Function (on)

data Tree a = Empty | Single !Int a | Bin !Int (Tree a) !Int (Tree a)
    deriving (Show)

minKey :: Tree a -> Int
minKey Empty = 0
minKey (Single n _) = n
minKey (Bin n _ _ _) = n

maxKey :: Tree a -> Int
maxKey Empty = 0
maxKey (Single n _) = n
maxKey (Bin _ _ n t) = n + maxKey t

shift :: Int -> Tree a -> Tree a
shift 0 a = a
shift _ Empty = Empty
shift i (Single n a) = Single (n + i) a
shift i (Bin n a m b) = Bin (n + i) a (m + i) b

empty :: Tree a
empty = Empty

singleton :: Int -> a -> Tree a
singleton = Single

(><) :: Tree a -> Tree a -> Tree a
(><) a b = Bin 0 a (maxKey a + 1) b

toList :: Tree a -> [(Int, a)]
toList = go 0
  where
    go _ Empty = []
    go i (Single n v) = [(i + n, v)]
    go i (Bin n a m b) = go (i + n) a ++ go (i + m) b

insert :: Int -> a -> Tree a -> Tree a
insert i v Empty = Single i v
insert i v (Single j w) | i < j =
    Bin i (Single 0 v) j (Single 0 w)
                        | otherwise =
    Bin j (Single 0 w) i (Single 0 v)
insert i v (Bin j a k b) | i < k =
    Bin (min i j) (insert (i - min i j) v $ shift (j - min i j) a) k b
                         | otherwise =
    Bin j a (min i k) (insert (i - min i k) v $ shift (min i k - k) b)

fromList :: [(Int, a)] -> Tree a
fromList = foldr (uncurry insert) Empty

prop_fromToList :: [(Int, Char)] -> Bool
prop_fromToList xs = sortBy (compare `on` fst) xs' == xs' && sort xs' == sort xs
    where xs' = toList (fromList xs)
