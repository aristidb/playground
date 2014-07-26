{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Newmodel where

import Data.Monoid

-- TODO: do not rely on list ordering so much?

data Scalar = SString String
    deriving (Show)

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
