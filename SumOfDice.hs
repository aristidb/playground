import Control.Applicative
import Control.Monad

type Dist a = [a]

die :: Int -> Dist Int
die n = [1..n]

sumOfDice :: Int -> Int -> Dist Int
sumOfDice k n = sum <$> replicateM k (die n)

sumOfDiceSeries :: [Int] -> Dist Int
sumOfDiceSeries = go . reverse
  where go [] = [1]
        go (n : ns) = do k <- go ns
                         sumOfDice k n

s2 :: [Int] -> Dist Int
s2 xs = go xs [1]
  where 
    go [] ks = ks
    go (n:ns) ks = do k <- ks
                      go ns (sumOfDice k n)

dist389 :: Dist Int
dist389 = sumOfDiceSeries [4,6]
