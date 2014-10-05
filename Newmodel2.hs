{-# LANGUAGE RecordWildCards #-}
module Newmodel2 where

import qualified Data.Map as M
import qualified Data.Set as S

data ScalarType = SUnit | SString
    deriving (Eq, Show)

data Type = Type {
      scalarType :: ScalarType
    , keys :: S.Set Key -- enforces sorting?
    , contextTypes :: M.Map ContextName Type
    }
    deriving (Eq, Show)

type Key = S.Set ContextName

type ContextName = String

valid :: Type -> Bool
valid Type{scalarType = _st, keys = ks, contextTypes = cs } = all (flip M.member cs) (S.toList $ S.unions $ S.toList ks)

{-
contexts :: Type -> [ContextName]
contexts = 
-}

scalar :: ScalarType -> Type
scalar st = Type { scalarType = st, keys = S.singleton S.empty, contextTypes = M.empty }

empty :: Type
empty = scalar SUnit

list :: ScalarType -> Type
list st = Type { scalarType = st, keys = S.empty, contextTypes = M.empty }

record :: S.Set Key -> M.Map ContextName Type -> Type
record = Type SUnit

embed :: Type -> M.Map ContextName Type -> Type
embed Type{..} cs = Type { scalarType = scalarType, keys = keys, contextTypes = M.union cs contextTypes }
