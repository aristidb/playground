import Control.Monad.Free
import Pipes
import qualified Pipes.Prelude as P
import Prelude hiding (lines)

line
    :: (Monad m)
    => Producer String m r -> Producer String m (Either r (Producer String m r))
line p = do
    x <- lift (next p)
    case x of
        Left   r        -> return (Left r)
        Right (str, p') -> do
            let (prefix, suffix) = span (/= '\n') str
            yield prefix
            case suffix of
                []        -> line p'
                ['\n']    -> return (Right                p' )
                '\n':rest -> return (Right (yield rest >> p'))

lines :: (Monad m) => Producer String m r -> Free (Producer String m) r
lines p = Free (fmap f (line p))
    where
    f x = case x of
        Left  r  -> Pure  r
        Right p' -> lines p'

source :: (Monad m) => Producer String m ()
source = each ["Test", "ing\n", "1", "\n2\n", "3"]

main = loop 0 (lines source)
    where
    loop n x = case x of
        Pure r -> return r
        Free p -> do
            putStrLn $ "Reading Line #" ++ show n 
            --x' <- run $ for p (lift . putStrLn)
            --putStrLn ""
            s <- P.foldl (++) [] id p
            putStrLn s
            loop (n + 1) x'

