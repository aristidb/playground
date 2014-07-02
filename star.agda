module star where

open import Data.Star
open import Relation.Binary
open import Relation.Nullary
open import Data.Nat
open import Data.Empty

data Suc : ℕ -> ℕ -> Set where
  suc! : ∀ {n} -> Suc n (suc n)

next : Suc =[ suc ]⇒ Suc
next {n} suc! = suc!

prev : ∀ {n m} -> Suc (suc n) (suc m) -> Suc n m
prev {n} suc! = suc!

Suc* : ℕ -> ℕ -> Set
Suc* = Star Suc

suc*-invalid : ∀ {n} -> ¬ (Suc* (suc n) 0)
suc*-invalid (() ◅ ε)
suc*-invalid {n} (suc! ◅ suc! ◅ xs) = suc*-invalid xs

next* : ∀ {n m} -> Suc* n m -> Suc* (suc n) (suc m)
next* = gmap suc next

prev* : ∀ {n m} -> Suc* (suc n) (suc m) -> Suc* n m
prev* ε = ε
prev* {n} (suc! ◅ xs) = suc! ◅ prev* xs

data LE : ℕ -> ℕ -> Set where
  zeroLE : ∀ {n} -> LE zero n
  sucLE : ∀ {n} {m} -> LE n m -> LE (suc n) (suc m)

right : ∀ {n m} -> LE n m -> LE n (suc m)
right zeroLE = zeroLE
right (sucLE x) = sucLE (right x)

LEtoSuc : ∀ n m -> LE n m -> Suc* n m
LEtoSuc .0 zero zeroLE = ε
LEtoSuc .0 (suc m) zeroLE = suc! ◅ next* (LEtoSuc 0 m zeroLE)
LEtoSuc .(suc n) (suc m) (sucLE {n} x) = next* (LEtoSuc n m x)

SucToLE : ∀ n m -> Suc* n m -> LE n m
SucToLE .0 zero ε = zeroLE
SucToLE .(suc n) (suc n) ε = sucLE (SucToLE n n ε)
SucToLE n zero (suc! ◅ xs) = ⊥-elim (suc*-invalid xs)
SucToLE n (suc m) (suc! ◅ xs) = right (SucToLE n m (prev* xs))