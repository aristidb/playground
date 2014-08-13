{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Newmodel where

import Data.Monoid
import qualified Data.Map as M

-- TODO: do not rely on list ordering so much?

{-
data Scalar = SString String
    deriving (Eq, Ord, Show)
-}
type Scalar = String

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
    | SeqC String Value3 [(Value3, Value3)] -- first Value3 is nil-Value
    deriving (Eq, Show)
-- ascending keys with depth

instance Ord Value3 where

instance Monoid Value3 where
    mempty = Nil
    mappend Nil b = b
    mappend a Nil = a
    mappend (ScalarV _) y@(ScalarV _) = y
    mappend x@(ScalarV _) (SeqC s y b) = SeqC s (x `mappend` y) b
    mappend (SeqC s x a) y@(ScalarV _) = SeqC s (x `mappend` y) a
    mappend (SeqC s1 x a) (SeqC s2 y b) | s1 == s2 = SeqC s1 (x `mappend` y) (a ++ b)
                                        | s1 < s2 = SeqC s1 (x `mappend` SeqC s2 y b) a
                                        | otherwise = SeqC s2 (SeqC s1 x a `mappend` y) b

embed :: String -> Value3 -> Value3 -> Value3
embed s k Nil = SeqC s Nil [(k, Nil)]
embed s k v@(ScalarV _) = SeqC s Nil [(k, v)]
embed s1 k v@(SeqC s2 x a) | s1 == s2 = SeqC s1 x (map (\(k0, v0) -> (k0 `mappend` k, v0)) a)
                           | s1 < s2 = SeqC s1 Nil [(k, v)]
                           | otherwise = SeqC s2 x (map (\(k0, v0) -> (k0, embed s1 k v0)) a)

newtype V = V [StreamItem]

data StreamItem = EnterContext String V | LeaveContext String V | Data V
