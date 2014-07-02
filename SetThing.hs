{-# LANGUAGE KindSignatures, DataKinds, GADTs, StandaloneDeriving, TypeOperators, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances, PolyKinds #-}
module SetThing where

import qualified Data.Set as S
import qualified Data.Map as M
import GHC.TypeLits
import Data.Type.Equality
import Data.Type.Bool
-- import Data.Proxy
-- import Unsafe.Coerce (unsafeCoerce)

data Type
    = TVoid
    | TUnit
    | TInteger
    | (::*::) Type Type
    | (::+::) Type Type
    | TSet [(Symbol, Type)]
    | TLabelled Symbol Type

data Value :: Type -> * where
    Unit :: Value TUnit
    I :: Integer -> Value TInteger
    (:*:) :: Value a -> Value b -> Value (a ::*:: b)
    A :: Value a -> Value (a ::+:: b)
    B :: Value b -> Value (a ::+:: b)
    -- Set :: S.Set (Value t) -> Value (TSet t)
    S :: Set cs -> Value (TSet cs)
    L :: Value a -> Value (TLabelled l a)

deriving instance Show (Value t)

l :: proxy l -> Value a -> Value (TLabelled l a)
l _ = L

data Set :: [(Symbol, Type)] -> * where
    Set :: S.Set (Row cs) -> Set cs

deriving instance Show (Set cs)

data Row :: [(Symbol, Type)] -> * where
    Nil :: Row '[]
    (:#) :: Value a -> Row cs -> Row ('(s, a) ': cs)

infixr 5 :#

deriving instance Show (Row cs)

type family Head (xs :: [a]) :: a
type instance Head (x ': xs) = x

type family Lookup (cs :: [(Symbol, Type)]) (s :: Symbol) :: Maybe Type where
    Lookup '[] a = Nothing
    Lookup ('(sc, t) ': cs) s = If (sc == s) (Just t) (Lookup cs s)

instance Eq (Value t) where
    Unit == Unit = True
    I x == I y = x == y
    a1 :*: b1 == a2 :*: b2 = a1 == a2 && b1 == b2
    A x == A y = x == y
    A _ == B _ = False
    B _ == A _ = False
    B x == B y = x == y
    S x == S y = x == y
    L x == L y = x == y
    _ == _ = error "Stupid GHC doesn't support GADT exhaustiveness checks properly, so you're on your own"

instance Ord (Value t) where
    Unit <= Unit = True
    I x <= I y = x <= y
    a1 :*: b1 <= a2 :*: b2 = (a1, b1) <= (a2, b2)
    A x <= A y = x <= y
    A _ <= B _ = True
    B _ <= A _ = False
    B x <= B y = x <= y
    -- Set a <= Set b = a <= b
    L x <= L y = x <= y
    _ <= _ = error "Stupid GHC doesn't support GADT exhaustiveness checks properly, so you're on your own"

instance Eq (Set cs) where
    Set x == Set y = x == y

instance Ord (Set cs) where
    Set x <= Set y = x <= y

instance Eq (Row cs) where
    Nil == Nil = True
    (a :# as) == (b :# bs) = a == b && as == bs
    _ == _ = error "Stupid GHC doesn't support GADT exhaustiveness checks properly, so you're on your own"

instance Ord (Row cs) where
    Nil <= Nil = True
    (a :# as) <= (b :# bs) = (a, as) <= (b, bs)
    _ <= _ = error "Stupid GHC doesn't support GADT exhaustiveness checks properly, so you're on your own"


{-
data AnyValue :: * where
    Any :: KnownType a => Value a -> AnyValue

data TypeS
    = SVoid
    | SUnit
    | SInteger
    | SProduct TypeS TypeS
    | SSum TypeS TypeS
    | SSet TypeS
    | SLabelled String TypeS
    deriving (Eq, Ord, Show)

class KnownType (a :: Type) where
    typeSing :: proxy a -> TypeS

instance KnownType TVoid where typeSing _ = SVoid
instance KnownType TUnit where typeSing _ = SUnit
instance KnownType TInteger where typeSing _ = SInteger
instance (KnownType x, KnownType y) => KnownType (x ::*:: y) where
    typeSing _ = SProduct (typeSing (Proxy :: Proxy x)) (typeSing (Proxy :: Proxy y))
instance (KnownType x, KnownType y) => KnownType (x ::+:: y) where
    typeSing _ = SSum (typeSing (Proxy :: Proxy x)) (typeSing (Proxy :: Proxy y))
instance (KnownType x) => KnownType (TSet x) where
    typeSing _ = SSet (typeSing (Proxy :: Proxy x))
instance (KnownSymbol l, KnownType x) => KnownType (TLabelled l x) where
    typeSing _ = SLabelled (symbolVal (Proxy :: Proxy l)) (typeSing (Proxy :: Proxy x))

sameType :: (KnownType a, KnownType b) => proxy a -> proxy b -> Maybe (a :~: b)
sameType x y | typeSing x == typeSing y = Just (unsafeCoerce Refl)
             | otherwise = Nothing

instance Eq AnyValue where
    Any x == Any y =
        case sameType x y of
            Just refl -> castWith (apply Refl refl) x == y
            Nothing -> False

instance Ord AnyValue where
    Any x <= Any y =
         case sameType x y of
            Just refl -> castWith (apply Refl refl) x <= y
            Nothing -> typeSing x <= typeSing y
-}
