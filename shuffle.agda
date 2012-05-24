module shuffle where

open import Data.List hiding (_∷ʳ_)

infixr 5 _∷ˡ_ _∷ʳ_

data Shuffle {A : Set} : (xs ys zs : List A) → Set where
  [] : Shuffle [] [] []
  _∷ˡ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle (a ∷ xs) ys (a ∷ zs)
  _∷ʳ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle xs (a ∷ ys) (a ∷ zs)

open import Data.Product hiding (map)

shuffles : {A : Set} (xs ys : List A) → List (∃ (Shuffle xs ys))
shuffles [] [] = (, []) ∷ []
shuffles [] (y ∷ ys) = map (λ t → , y ∷ʳ proj₂ t) (shuffles [] ys)
shuffles (x ∷ xs) [] = map (λ t → , x ∷ˡ proj₂ t) (shuffles xs [])
shuffles (x ∷ xs) (y ∷ ys) = {!shuffles xs ys!}

module Test where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  x : Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (1 ∷ 3 ∷ 2 ∷ 4 ∷ [])
  x = 1 ∷ˡ 3 ∷ʳ 2 ∷ˡ 4 ∷ʳ []

  y : ¬ Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (2 ∷ 1 ∷ 3 ∷ 4 ∷ [])
  y = λ ()
