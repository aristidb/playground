module lens where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

_f≡_ : ∀ {l} {A : Set l} {B : A → Set l} → (f g : (x : A) → B x) → Set l
f f≡ g = ∀ x → f x ≡ g x

record Lens (i o : Set → Set) : Set₁ where
  field
    view : {a : Set} → i a → o a
    set : {a b : Set} → o b → i a → i b

  field
    .viewSet : {a b : Set} {A : i a} {B : o b} → view (set B A) ≡ B
    .setView : {a : Set} {A : i a} → set (view A) A ≡ A
    .setSet : {a b c : Set} {A : i a} {B : o b} {C : o c} → set C (set B A) ≡ set C A

Proj1 : {b : Set} → Lens (λ a → a × b) id
Proj1 {b} = record {
              view = proj₁;
              set = λ a p → a , proj₂ p;
              viewSet = refl;
              setView = refl;
              setSet = refl }

record IsProfunctor (p : Set → Set → Set) : Set₁ where
  field
    dimap : {a b c d : Set} → (a → b) → (c → d) → p b c → p a d

  field
    .profunctorIdentity : {a c : Set} → dimap (id {A = a}) (id {A = c}) f≡ id
    .profunctorCompose : {a b c d e f : Set} →
                         (f : b → c) (g : a → b) (h : d → e) (i : c → d) →
                         dimap (f ∘ g) (h ∘ i) f≡ (dimap g h ∘ dimap f i)

fnProfunctor : IsProfunctor (λ a b → a → b)
fnProfunctor = record {
                 dimap = dimap;
                 profunctorIdentity = λ _ → refl;
                 profunctorCompose = λ f₁ g h i x → refl }
  where dimap : {a b c d : Set} → (a → b) → (c → d) → (b → c) → (a → d)
        dimap f g p = g ∘ p ∘ f
