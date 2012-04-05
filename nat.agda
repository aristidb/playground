module nat where

open import Data.Nat
import Data.Nat.Properties as NP
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary

data M : Set where
  z : M
  s : M → M

nobigger : (d : ℕ) → (∀ x → x < d) → ⊥
nobigger d f = irrefl _≡_.refl (f d)
  where open StrictTotalOrder NP.strictTotalOrder