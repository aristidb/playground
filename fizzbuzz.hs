import Data.Maybe
import Control.Applicative
import Control.Monad
import Data.Monoid

fizzbuzz :: Integer -> String
fizzbuzz i = fromMaybe (show i) $ mconcat . map (\(n,s) -> s <$ guard (i `rem` n == 0)) $ [(3, "fizz"), (5, "buzz")]