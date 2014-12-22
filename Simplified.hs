-- ultimately we want arbitrary (unsorted) orderings, but I want to clarify concepts with simplified types that do not support that

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Simplified where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Monoid
import Data.List hiding (splitAt)
import Prelude hiding (splitAt)

type Value = S.Set Fact

type Context = M.Map String Value

data Fact = Fact { context :: Context, scalarValue :: Scalar }
  deriving (Eq, Ord)

instance Show Fact where
    show (Fact cs v) | M.null cs = show v
                     | otherwise = "Fact (" ++ show cs ++ ") (" ++ show v ++ ")"

data Scalar = SUnit | SString String | SNumber Double
  deriving (Eq, Ord, Show)

{- TYPES:
    * Cardinality constraints by context
    * Scalar type constraints
-}

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

splitAt :: String -> Value -> (M.Map (Maybe Value) Value)
splitAt c fs = M.unionsWith mappend $ map (uncurry M.singleton . extractOne) $ S.toList fs
  where
    extractOne :: Fact -> (Maybe Value, Value)
    extractOne (Fact cs sv) =
      case M.lookup c cs of
        Just cv -> (Just cv, S.singleton $ Fact (M.delete c cs) sv)
        Nothing -> (Nothing, S.singleton $ Fact cs sv)

ds1 :: Value
ds1 = mconcat $ map ctx entries
  where
    ctx (y,m,d,r,dur) =
        embedContext
            (M.fromList ([
                ("year",number y),
                ("month",number m),
                ("day",number d)
            ] ++ case dur of
                   Nothing -> []
                   Just dv -> [("duration",embed "unit" (string "years") $ number dv)]
            ))
            (number r)
    entries = [ (2014,1,2,3.92,Nothing), (2014,2,3,3.55,Nothing), (2014,3,3,3.55,Just 10) ]

data Nested = Nested [String] Node
    deriving (Eq, Ord, Show)

-- not currently encoded in type: leafs should only occur when the list of contexts is empty
data Node = Branch (M.Map (Maybe Nested) Node) | Leaf (S.Set Scalar)
    deriving (Eq, Show)

instance Ord Node where
    Leaf a <= Leaf b = a <= b
    Branch a <= Branch b = a <= b
    Leaf _ <= Branch _ = True
    Branch _ <= Leaf _ = False

toNested :: Value -> Nested
toNested fs = Nested keys (toNode keys fs)
  where
    keys = S.toList . S.unions . map (S.fromList . M.keys . context) . S.toList $ fs

toNode :: [String] -> Value -> Node
toNode [] fs = Leaf $ S.map scalarValue fs
toNode (key0:keys') fs = Branch $ M.fromList $ map (\(k, v) -> (fmap toNested k, toNode keys' v)) (M.toList (splitAt key0 fs))

toFlat :: Nested -> Value
toFlat (Nested k x) = toFlat' k x

toFlat' :: [String] -> Node -> Value
toFlat' [] (Leaf sv) = S.map (Fact M.empty) sv
toFlat' (k:ks) (Branch m) = S.unions $ map (uncurry inner) $ M.toList m
  where
    inner Nothing v = toFlat' ks v
    inner (Just kv) v = embed k (toFlat kv) (toFlat' ks v)
toFlat' _ _ = error "Branch vs leaf error"

rearrange :: [String] -> Nested -> Nested
rearrange ks v = Nested ks (toNode ks (toFlat v))

merge :: Nested -> Nested -> Nested
merge (Nested k1 m) (Nested k2 n) = Nested ks $ mergeNode m' n'
  where
    ks = nub (k1 ++ k2)
    Nested _ m' = rearrange ks (Nested k1 m)
    Nested _ n' = rearrange ks (Nested k2 n)

mergeNode :: Node -> Node -> Node
mergeNode (Leaf a) (Leaf b) = Leaf (a <> b)
mergeNode (Branch m) (Branch n) = Branch $ M.unionWith mergeNode m n
mergeNode _ _ = error "Branch vs leaf error"

printNested :: Int -> Nested -> IO ()
printNested ind (Nested ks m) = printNested' ind ks m

printNested' :: Int -> [String] -> Node -> IO ()
printNested' ind [] (Leaf svs) = flip mapM_ (S.toList svs) $ \sv -> indented ind (show sv)
printNested' ind (k:ks) (Branch m) = flip mapM_ (M.toList m) $ \(kv,v) ->
  do
    indented ind k
    case kv of
      Nothing -> indented (ind+1) "<SKIP>"
      Just x -> printNested (ind+1) x
    indented (ind+1) "=>"
    printNested' (ind+1) ks v
printNested' _ _ _ = error "Branch vs leaf error"

indented :: Int -> String -> IO ()
indented ind str = putStrLn $ replicate ind '\t' ++ str
