module vec where

open import Data.Vec
open import Data.Nat

xlast : {A : Set} {n : ℕ} → Vec A (suc n) → A
xlast (x ∷ []) = x
xlast {n = suc n} (x ∷ xs) = xlast xs
