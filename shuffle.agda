module shuffle where

open import Data.List hiding (_∷ʳ_)
open import Data.List.Any
open import Data.Sum
open import Function.Inverse
open import Relation.Binary.PropositionalEquality

open Membership-≡
module L = Data.List
module S = Data.Sum

infixr 5 _∷ˡ_ _∷ʳ_

data Shuffle {A : Set} : (xs ys zs : List A) → Set where
  [] : Shuffle [] [] []
  _∷ˡ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle (a ∷ xs) ys (a ∷ zs)
  _∷ʳ_ : ∀ {xs ys zs} a → Shuffle xs ys zs → Shuffle xs (a ∷ ys) (a ∷ zs)

sym-shuffle : {A : Set} {xs ys zs : List A} → Shuffle xs ys zs → Shuffle ys xs zs
sym-shuffle [] = []
sym-shuffle (a ∷ˡ t) = a ∷ʳ sym-shuffle t
sym-shuffle (a ∷ʳ t) = a ∷ˡ sym-shuffle t

data Subsequence {A : Set} : (xs ys : List A) → Set where
  ε : Subsequence [] []
  keep : ∀ {xs ys} a → Subsequence xs ys → Subsequence (a ∷ xs) (a ∷ ys)
  skip : ∀ {xs ys} a → Subsequence xs ys → Subsequence xs (a ∷ ys)

shuffle⇒subsequence : {A : Set} {xs ys zs : List A} → Shuffle xs ys zs → Subsequence xs zs
shuffle⇒subsequence [] = ε
shuffle⇒subsequence (a ∷ˡ x) = keep a (shuffle⇒subsequence x)
shuffle⇒subsequence (a ∷ʳ x) = skip a (shuffle⇒subsequence x)

shuffle-complete : {A : Set} {xs ys zs : List A} → Shuffle xs ys zs → ∀ x → (x ∈ xs ⊎ x ∈ ys) ↔ x ∈ zs
shuffle-complete {A = A} sh₁ x = record {
                                   to = record { _⟨$⟩_ = to sh₁; cong = cong _ };
                                   from = record { _⟨$⟩_ = from sh₁; cong = cong _ };
                                   inverse-of =
                                     record {
                                     left-inverse-of = left-inverse sh₁;
                                     right-inverse-of = right-inverse sh₁ } }
  where to : {xs ys zs : List A} {x : A} → Shuffle xs ys zs → x ∈ xs ⊎ x ∈ ys → x ∈ zs
        to [] (inj₁ ())
        to (a ∷ˡ sh) (inj₁ (here px)) = here px
        to (a ∷ˡ sh) (inj₁ (there p)) = there (to sh (inj₁ p))
        to (a ∷ʳ sh) (inj₁ p) = there (to sh (inj₁ p))
        to [] (inj₂ ())
        to (a ∷ˡ sh) (inj₂ q) = there (to sh (inj₂ q))
        to (a ∷ʳ sh) (inj₂ (here qx)) = here qx
        to (a ∷ʳ sh) (inj₂ (there q)) = there (to sh (inj₂ q))

        from : {xs ys zs : List A} {x : A} → Shuffle xs ys zs → x ∈ zs → x ∈ xs ⊎ x ∈ ys
        from [] ()
        from (a ∷ˡ sh) (here px) = inj₁ (here px)
        from (a ∷ˡ sh) (there p) = S.map there (λ z → z) (from sh p)
        from (a ∷ʳ sh) (here px) = inj₂ (here px)
        from (a ∷ʳ sh) (there p) = S.map (λ z → z) there (from sh p)

        left-inverse : {xs ys zs : List A} {x : A} (sh : Shuffle xs ys zs) (p : x ∈ xs ⊎ x ∈ ys) → from sh (to sh p) ≡ p
        left-inverse [] (inj₁ ())
        left-inverse (a ∷ˡ sh) (inj₁ (here px)) = refl
        left-inverse (a ∷ˡ sh) (inj₁ (there p)) with from sh (to sh (inj₁ p)) | left-inverse sh (inj₁ p)
        left-inverse (a ∷ˡ sh) (inj₁ (there p)) | .(inj₁ p) | refl = refl
        left-inverse (a ∷ʳ sh) (inj₁ p) with from sh (to sh (inj₁ p)) | left-inverse sh (inj₁ p)
        left-inverse (a ∷ʳ sh) (inj₁ p) | .(inj₁ p) | refl = refl
        left-inverse [] (inj₂ ())
        left-inverse (a ∷ˡ sh) (inj₂ q) with from sh (to sh (inj₂ q)) | left-inverse sh (inj₂ q)
        left-inverse (a ∷ˡ sh) (inj₂ q) | .(inj₂ q) | refl = refl
        left-inverse (a ∷ʳ sh) (inj₂ (here px)) = refl
        left-inverse (a ∷ʳ sh) (inj₂ (there q)) with from sh (to sh (inj₂ q)) | left-inverse sh (inj₂ q)
        left-inverse (a ∷ʳ sh) (inj₂ (there q)) | .(inj₂ q) | refl = refl

        right-inverse : {xs ys zs : List A} {x : A} (sh : Shuffle xs ys zs) (p : x ∈ zs) → to sh (from sh p) ≡ p
        right-inverse [] ()
        right-inverse (a ∷ˡ sh) (here px) = refl
        right-inverse (a ∷ˡ sh) (there p) with from sh p | right-inverse sh p
        right-inverse (a ∷ˡ sh) (there .(to sh (inj₁ f))) | inj₁ f | refl = refl
        right-inverse (a ∷ˡ sh) (there .(to sh (inj₂ g))) | inj₂ g | refl = refl
        right-inverse (a ∷ʳ sh) (here px) = refl
        right-inverse (a ∷ʳ sh) (there p) with from sh p | right-inverse sh p
        right-inverse (a ∷ʳ sh) (there .(to sh (inj₁ f))) | inj₁ f | refl = refl
        right-inverse (a ∷ʳ sh) (there .(to sh (inj₂ g))) | inj₂ g | refl = refl

open import Data.Product

infixr 5 _∷ˡ∃_ _∷ʳ∃_

_∷ˡ∃_ : {A : Set} {xs ys : List A} → (x : A) → ∃ (Shuffle xs ys) → ∃ (Shuffle (x ∷ xs) ys)
x ∷ˡ∃ (_ , sh) = , x ∷ˡ sh

_∷ʳ∃_ : {A : Set} {xs ys : List A} → (y : A) → ∃ (Shuffle xs ys) → ∃ (Shuffle xs (y ∷ ys))
x ∷ʳ∃ (_ , sh) = , x ∷ʳ sh

-- FIXME: currently only spits out a partial list of shuffles
shuffles : {A : Set} (xs ys : List A) → List (∃ (Shuffle xs ys))
shuffles [] [] = (, []) ∷ []
shuffles [] (y ∷ ys) = L.map (λ t → y ∷ʳ∃ t) (shuffles [] ys)
shuffles (x ∷ xs) [] = L.map (λ t → x ∷ˡ∃ t) (shuffles xs [])
shuffles (x ∷ xs) (y ∷ ys) = concatMap (λ t → (x ∷ˡ∃ y ∷ʳ∃ t) ∷ (y ∷ʳ∃ x ∷ˡ∃ t) ∷ []) (shuffles xs ys)

module Test where
  open import Data.Nat
  open import Relation.Nullary

  x : Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (1 ∷ 3 ∷ 2 ∷ 4 ∷ [])
  x = 1 ∷ˡ 3 ∷ʳ 2 ∷ˡ 4 ∷ʳ []

  y : ¬ Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (2 ∷ 1 ∷ 3 ∷ 4 ∷ [])
  y = λ ()

  z : Shuffle (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ []) (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  z = 1 ∷ˡ 2 ∷ˡ 3 ∷ʳ 4 ∷ʳ []

  t : _
  t = shuffles (1 ∷ 2 ∷ []) (3 ∷ 4 ∷ [])

