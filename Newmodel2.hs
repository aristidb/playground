{-# LANGUAGE RecordWildCards #-}
module Newmodel2 where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text (Text)
import Data.Monoid
-- import qualified Data.Vector as V

data ScalarType = TUnit | TString
    deriving (Eq, Show)

-- FIXME
data Type = Type {
      scalarType :: ScalarType
    , keys :: S.Set Key -- enforces sorting?
    , contextTypes :: M.Map ContextName Type
    -- TODO: cardinality
    }
    deriving (Eq, Show)

type Key = S.Set ContextName

type ContextName = String

validType :: Type -> Bool
validType Type{..} = all (flip M.member contextTypes) (S.toList $ S.unions $ S.toList keys)

scalar :: ScalarType -> Type
scalar st = Type { scalarType = st, keys = S.singleton S.empty, contextTypes = M.empty }

empty :: Type
empty = scalar TUnit

-- FIXME, there is nothing list-like without a context, so either fix Value or "list"
list :: ScalarType -> Type
list st = Type { scalarType = st, keys = S.empty, contextTypes = M.empty }

record :: S.Set Key -> M.Map ContextName Type -> Type
record = Type TUnit

embedType :: Type -> M.Map ContextName Type -> Type
embedType Type{..} cs = Type { scalarType = scalarType, keys = keys, contextTypes = M.union cs contextTypes }

subType :: Type -> ContextName -> Type
subType (Type st ks cs) c = Type st (S.map (S.delete c) ks) (M.delete c cs)

data ScalarValue = SUnit | SString Text
    deriving (Eq, Show)

data Value =
    Scalar ScalarValue |
    WithContext ContextName Value [(Value, Value)]
    deriving (Eq, Show)

validValue :: Value -> Bool
validValue v = isStrictlyMonotonic (contextList v)
  where isStrictlyMonotonic xs = and $ zipWith (<) xs (tail xs)

typeCheck :: Type -> Value -> Bool
typeCheck t v = validType t && validValue v && typeCheck' t v
  where
    typeCheck' (Type st _ _) (Scalar sv) =
        case (st, sv) of
          (TUnit, SUnit) -> True
          (TString, SString _) -> True
          _ -> False
    typeCheck' (Type _st _ks cs) (WithContext c x xs) =
        case M.lookup c cs of
          Just ct -> typeCheck sub x && all (typeCheck ct) (map snd xs)
          Nothing -> False
      where sub = subType t c
  -- TODO: check keys

contextList :: Value -> [ContextName]
contextList (Scalar _) = []
contextList (WithContext cn v vs) = cn : merge (contextList v : map (\(_, x) -> contextList x) vs)

instance Monoid Value where
    mempty = Scalar SUnit

    mappend x (Scalar SUnit) = x
    mappend (Scalar SUnit) y = y
    mappend (Scalar _) y@(Scalar _) = y
    mappend x@(Scalar _) (WithContext b y ys) = WithContext b (x `mappend` y) ys
    mappend (WithContext a x xs) y@(Scalar _) = WithContext a (x `mappend` y) xs
    mappend v@(WithContext a x xs) w@(WithContext b y ys)
        | a == b = WithContext a (x `mappend` y) (xs ++ ys) -- TODO: xs ++ ys replace by key-aware
        | a < b = WithContext a (x `mappend` w) xs
        | otherwise = WithContext b (v `mappend` y) ys

unit :: Value
unit = Scalar SUnit

string :: Text -> Value
string x = Scalar (SString x)

embed :: ContextName -> Value -> Value -> Value
embed a k v@(Scalar _) = WithContext a unit [(k, v)]
embed a k (WithContext b v vs) | a == b = WithContext a v (map (\(k0, v0) -> (k0 `mappend` k, v0)) vs)

merge :: Ord a => [[a]] -> [a]
merge = foldr merge2 []

merge2 :: Ord a => [a] -> [a] -> [a]
merge2 [] ys = ys
merge2 xs [] = xs
merge2 xs@(x:xs_) ys@(y:ys_) | x == y = x : merge2 xs_ ys_
                             | x < y = x : merge2 xs_ ys
                             | otherwise = y : merge2 xs ys_
