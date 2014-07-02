{-# LANGUAGE KindSignatures, DataKinds, GADTs #-}
module Test where

-- data X = A | B
data A
data B

data E :: * -> * where
    AA :: E A
    BB :: E B

foo :: E t -> E t -> ()
foo AA AA = ()
foo BB BB = ()
