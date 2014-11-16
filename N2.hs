{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}
module N2 where

data X a b = X a b

class Get x o where
    get :: x -> o

instance Get (X a b) a where
    get (X a _) = a

instance Get (X a b) b where
    get (X _ b) = b
