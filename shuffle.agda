module shuffle where

open import Data.List hiding (_∷ʳ_)

infixr 5 _∷ˡ_ _∷ʳ_

data Shuffle {A : Set} : (xs : List A) (ys : List A) (zs : List A) → Set where
  [] : Shuffle [] [] []
  _∷ˡ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle (a ∷ xs) ys (a ∷ zs)
  _∷ʳ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle xs (a ∷ ys) (a ∷ zs)

module Test where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  x : Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (1 ∷ 3 ∷ 2 ∷ 4 ∷ [])
  x = 1 ∷ˡ 3 ∷ʳ 2 ∷ˡ 4 ∷ʳ []

  y : ¬ Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (2 ∷ 1 ∷ 3 ∷ 4 ∷ [])
  y = λ ()
