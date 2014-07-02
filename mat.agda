module mat where

open import Data.Nat
open import Data.Vec

Matrix : Set → ℕ → ℕ → Set 
Matrix A n m = Vec (Vec A n) m

_*₁_ : {i : ℕ} → ℕ → Vec ℕ i → Vec ℕ i
n *₁ v = map (_*_ n) v

_×₁_ : {i j : ℕ} → Matrix ℕ i j → Vec ℕ j → Vec ℕ i
[] ×₁ b = replicate 0
(a ∷ as) ×₁ (b ∷ bs) = zipWith _+_ (b *₁ a) (as ×₁ bs)

_×_ : {i j k : ℕ} → Matrix ℕ i j → Matrix ℕ j k → Matrix ℕ i k
a × b = map (_×₁_ a) b

a : Matrix ℕ 2 2
a = (1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ []

b : Matrix ℕ 2 3
b = (1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ (5 ∷ 6 ∷ []) ∷ []
