module lens where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

_f≡_ : ∀ {l} {A : Set l} {B : A → Set l} → (f g : (x : A) → B x) → Set l
f f≡ g = ∀ x → f x ≡ g x

record Lens {I : Set₁} (i o : I → Set) : Set₁ where
  constructor lens

  field
    view : {a : I} → i a → o a
    set : {a b : I} → o b → i a → i b

  field
    .viewSet : {a b : I} {A : i a} {B : o b} → view (set B A) ≡ B
    .setView : {a : I} {A : i a} → set (view A) A ≡ A
    .setSet : {a b c : I} {A : i a} {B : o b} {C : o c} → set C (set B A) ≡ set C A

Proj1 : {b : Set} → Lens (λ a → a × b) id
Proj1 {b} = record {
              view = proj₁;
              set = λ a p → a , proj₂ p;
              viewSet = refl;
              setView = refl;
              setSet = refl }

record Iso {I : Set₁} (i o : I → Set) : Set₁ where
  constructor iso

  field
    hither : ∀ {a} → i a → o a
    yon : ∀ {a} → o a → i a

  field
    .hitherYon : ∀ {a} x → (hither {a} ∘ yon {a}) x ≡ x
    .yonHither : ∀ {a} x → (yon {a} ∘ hither {a}) x ≡ x

Swap : Iso (λ p → proj₁ p × proj₂ p) (λ p → proj₂ p × proj₁ p)
Swap = record { hither = swap; yon = swap; hitherYon = hitherYon; yonHither = sym ∘ hitherYon }
  where hitherYon : {A B : Set} (x : A × B) → proj₁ x , proj₂ x ≡ x
        hitherYon _ = refl

record IsProfunctor (p : Set → Set → Set) : Set₁ where
  field
    dimap : {a b c d : Set} → (a → b) → (c → d) → p b c → p a d

  lmap : ∀ {a b c} → (a → b) → p b c → p a c
  lmap f = dimap f id

  rmap : ∀ {a b c} → (b → c) → p a b → p a c
  rmap f = dimap id f

  field
    .profunctorIdentity : {a c : Set} → dimap (id {A = a}) (id {A = c}) f≡ id
    .profunctorCompose : {a b c d e : Set} →
                         (f : b → c) (g : a → b) (h : d → e) (i : c → d) →
                         dimap (f ∘ g) (h ∘ i) f≡ (dimap g h ∘ dimap f i)

fnProfunctor : IsProfunctor (λ a b → a → b)
fnProfunctor = record {
                 dimap = dimap;
                 profunctorIdentity = λ _ → refl;
                 profunctorCompose = λ f₁ g h i x → refl }
  where dimap : {a b c d : Set} → (a → b) → (c → d) → (b → c) → (a → d)
        dimap f g p = g ∘ p ∘ f

{-
record Exchange {I : Set₁} (i o : I → Set) : Set₁ where
  constructor exch
  field buy : ∀ a → i a → o a
        sell : ∀ a → o a → i a
-}

Review : (a b : Set) → Set
Review a b = b

reviewProfunctor : IsProfunctor Review
reviewProfunctor = record {
                     dimap = λ f g → g;
                     profunctorIdentity = λ _ → refl;
                     profunctorCompose = λ f g h i x → refl }

Forget : (r a b : Set) → Set
Forget r a b = a → r

forgetProfunctor : ∀ r → IsProfunctor (Forget r)
forgetProfunctor r = record {
                       dimap = λ f g p → p ∘ f;
                       profunctorIdentity = λ _ → refl;
                       profunctorCompose = λ f g h i x → refl }

IsoProfunctor : {I : Set₁} → (i o : I → Set) → Set₁
IsoProfunctor i o = ∀ {k a b} → IsProfunctor k → k (i a) (i b) → k (o a) (o b)

IsoFromNaive : ∀ {I i o} → Iso {I} i o → IsoProfunctor {I} i o
IsoFromNaive xiso pro = dimap yon hither
  where open Iso xiso
        open IsProfunctor pro

IsoToNaive : ∀ {I i o} → IsoProfunctor {I} i o → Iso {I} i o
IsoToNaive pro = iso (λ {a} → {!pro {a = a} reviewProfunctor!})
                   (λ {a} → {!pro {b = a} (forgetProfunctor _) id!})
                   {!!}
                   {!!}
