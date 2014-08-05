{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Newmodel where

import Data.Monoid
import qualified Data.Map as M

-- TODO: do not rely on list ordering so much?

data Scalar = SString String
    deriving (Eq, Ord, Show)

newtype Value = Value [Fact]
    deriving (Show, Monoid)

-- facts are normalised such that only scalars can be their values
data Fact = Fact [Context] Scalar
    deriving (Show)

data Context = Context String Value
    deriving (Show)

scalarValue :: Scalar -> Value
scalarValue s = Value [Fact [] s]

embedValue :: [Context] -> Value -> Value
embedValue ctx (Value fs) = Value (map (\(Fact c1 s) -> Fact (ctx++c1) s) fs)

newtype Value2 = Value2 (M.Map String Fact2)
    deriving (Eq, Show)

data Fact2
    = ScalarF Scalar
    | MapContext (M.Map Value2 Value2)
    | SeqContext [Value2]
    deriving (Eq, Show)

data Value3
    = Nil
    | ScalarV Scalar
    | MapC String (M.Map Value3 Value3) -- Nil key for "this context not used here"
    | SeqC String Value3 [Value3] -- first Value3 is nil-Value
    deriving (Eq, Show)
-- ascending keys with depth

instance Ord Value3 where

instance Monoid Value3 where
    mempty = Nil
    mappend Nil b = b
    mappend a Nil = a
    mappend (MapC s1 a) (MapC s2 b) | s1 == s2 = MapC s1 (M.union a b)
                                    | s1 < s2 = MapC s1 (M.insert Nil (MapC s2 b) a)
                                    | s1 > s2 = MapC s2 (M.insert Nil (MapC s1 a) b)
