module test where

open import Data.Nat
open import Data.List

range : ℕ -> ℕ -> List ℕ
range zero zero = zero ∷ []
range zero (suc n) = zero ∷ map suc (range zero n)
range (suc a) zero = []
range (suc a) (suc b) = map suc (range a b)

range2 : ℕ -> ℕ -> List ℕ
range2 a zero = []
range2 a (suc n) = a ∷ range2 a n

range′ : ℕ -> ℕ -> List ℕ
range′ a b = range2 a (b ∸ a)
