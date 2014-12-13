-- ultimately we want arbitrary (unsorted) orderings, but I want to clarify concepts with simplified types that do not support that

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Simplified where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Monoid
import Data.List

type Value = S.Set Fact

type Context = M.Map String Value

data Fact = Fact { context :: Context, scalarValue :: Scalar }
  deriving (Eq, Ord)

instance Show Fact where
    show (Fact cs v) | M.null cs = show v
                     | otherwise = "Fact (" ++ show cs ++ ") (" ++ show v ++ ")"

data Scalar = SUnit | SString String | SNumber Double
  deriving (Eq, Ord, Show)

scalar :: Scalar -> Value
scalar s = S.singleton $ Fact M.empty s

unit :: Value
unit = scalar SUnit

string :: String -> Value
string = scalar . SString

number :: Double -> Value
number = scalar . SNumber

embed :: String -> Value -> Value -> Value
embed ck cv v = S.map (\(Fact cs w) -> Fact (M.insert ck cv cs) w) v

embedContext :: Context -> Value -> Value
embedContext cs' v = S.map (\(Fact cs w) -> Fact (M.union cs' cs) w) v

extract :: String -> (Value -> Bool) -> Value -> Value
extract ck cvp = S.filter check
  where
    check (Fact cs _) =
      case M.lookup ck cs of
        Just cv -> cvp cv
        Nothing -> False

contextRanges :: Value -> M.Map String (S.Set Value)
contextRanges = M.unionsWith mappend . map (M.map S.singleton . context) . S.toList

splitCommon :: Value -> (Context, Value)
splitCommon v = (common, S.map strip v)
  where
    common = M.mapMaybe extractOne $ contextRanges v
    extractOne s =
      case S.minView s of
        Just (a, b) | S.null b -> Just a
        _ -> Nothing
    strip (Fact cs sv) = Fact (foldl' (\csx k -> M.delete k csx) cs (M.keys common)) sv

ds1 :: Value
ds1 = S.fromList $ map (\(y,m,d,r) -> undefined) undefined
