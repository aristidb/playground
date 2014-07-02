{-# LANGUAGE TypeFamilies, DataKinds, GADTs, PolyKinds, TypeOperators, UndecidableInstances, StandaloneDeriving, ScopedTypeVariables, DeriveDataTypeable, ConstraintKinds, DefaultSignatures #-}
module Datamodel where

import Data.Text (Text)
import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Proxy
import Data.Typeable

type family Lookup a xs :: t where
    Lookup a '[] = Nothing
    Lookup a ('(b, v) ': xs) = If (a == b) (Just v) (Lookup a xs)

type family FromMaybe a :: b where
    FromMaybe (Just a) = a

data Type =
    TInteger |
    TString |
    TProduct [(Symbol, Type)] |
    TSum [(Symbol, Type)] |
    TTable Type PathDescriptor

class (Show a, Typeable a) => ValueType a where -- TODO: m
    type TypeDescription a :: Type

    type PathType a (d :: PathDescriptor) :: *
    type PathType a IdentityD = a

    extractPath :: Path d (TypeDescription a) b -> a -> PathType a d
    default extractPath :: (PathType a IdentityD ~ a) => Path d (TypeDescription a) b -> a -> PathType a d
    extractPath Identity x = x
    extractPath _ _ = error "Unsatisfiable"

instance ValueType Integer where
    type TypeDescription Integer = TInteger

instance ValueType Text where
    type TypeDescription Text = TString

instance (ValueType a, ValueType b) => ValueType (Either a b) where
    type TypeDescription (Either a b) = TSum '[ '("Left", TypeDescription a), '("Right", TypeDescription b) ]

    type PathType (Either a b) IdentityD = Either a b
    type PathType (Either a b) (SumMemberD "Left" d) = Maybe (PathType a d)
    type PathType (Either a b) (SumMemberD "Right" d) = Maybe (PathType b d)

    extractPath Identity x = x
    extractPath (SumMember symb p) x =
        case (x, sameSymbol symb (Proxy :: Proxy "Left"), sameSymbol symb (Proxy :: Proxy "Right")) of
            (Left l, Just Refl, _) -> Just (extractPath p l)
            (Left _, _, Just Refl) -> Nothing
            (Right r, _, Just Refl) -> Just (extractPath p r)
            (Right _, Just Refl, _) -> Nothing
            (_, Nothing, Nothing) -> error "Impossible"
    extractPath _ _ = error "Unsatisfiable"

data PathDescriptor =
    IdentityD |
    ProductMemberD Symbol PathDescriptor |
    SumMemberD Symbol PathDescriptor |
    TableMemberD PathDescriptor PathDescriptor

data Path :: PathDescriptor -> Type -> Type -> * where
    Identity :: Path IdentityD a a
    ProductMember :: (KnownSymbol sym, Lookup sym xs ~ Just a) => Proxy sym -> Path d a b -> Path (ProductMemberD sym d) (TProduct xs) b
    SumMember :: (KnownSymbol sym, Lookup sym xs ~ Just a) => Proxy sym -> Path d a b -> Path (SumMemberD sym d) (TSum xs) b
    -- TableMember :: Path d -> PathType??

deriving instance Show (Path d a b)


data Foo = Foo { a :: Integer, b :: Text }
    deriving (Show, Eq, Typeable)

instance ValueType Foo where
    type TypeDescription Foo = TProduct '[ '("a", TInteger), '("b", TString) ]

    type PathType Foo IdentityD = Foo
    type PathType Foo (ProductMemberD "a" d) = PathType Integer d
    type PathType Foo (ProductMemberD "b" d) = PathType Text d

    extractPath Identity x = x
    extractPath (ProductMember symb p) (Foo x y) =
        case sameSymbol symb (Proxy :: Proxy "a") of
            Just Refl -> extractPath p x
            Nothing -> case sameSymbol symb (Proxy :: Proxy "b") of
                          Just Refl -> extractPath p y
                          Nothing -> error "Unsatisfiable"
    extractPath _ _ = error "Unsatisfiable"
