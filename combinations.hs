import Control.Monad

testIn xin n xs = all (\t -> length (filter (\(x,y) -> x==t) xs) == n) xin
testOut xout n m xs = all (\t -> let i = length (filter (\(x,y) -> y==t) xs) in i >= n && i <= m) xout
f xin xout nin nout1 nout2 = filter (\xs -> testIn xin nin xs && testOut xout nout1 nout2 xs) $ filterM (const [False,True]) [(x,y) | x <- xin, y <- xout]
g a b n m1 m2 = f [1 :: Int ..a] [1 :: Int ..b] n m1 m1

main = mapM_ print $ do a <- [2..]; b <- [a+1..a*2]; n <- [2..b-1]; m <- [2,3]; xs <- return (g a b n m (m+1)); return (a,b,n,m,take 1 xs)