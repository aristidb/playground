module foralllist where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Function.Inverse

F : Set₁
F = (A : Set) → List A → List A

G : Set
G = (n : ℕ) → List (Fin n)
