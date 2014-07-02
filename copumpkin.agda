module copumpkin where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data _≡_ {A : Set} : (a b : A) → Set where
  refl : ∀ {a} → a ≡ a

f : ℕ → Set
f zero = ⊤
f (suc n) = ⊥

sdiff : ℕ → ℕ → ℕ
sdiff zero zero = zero
sdiff zero (suc m) = suc (sdiff zero m)
sdiff (suc n) zero = suc (sdiff n zero)
sdiff (suc n) (suc m) = sdiff n m

s0 : ∀ {x} → sdiff x x ≡ zero
s0 {zero} = refl
s0 {suc n} = s0 {n}

w : ∀ {x y} → x ≡ y → f (sdiff x y)
w {x} refl with sdiff x x | s0 {x}
w refl | .zero | refl = tt

≡-pred : ∀ {n m} → suc n ≡ suc m → n ≡ m
≡-pred refl = refl

noAbsurd : ∀ n → n ≡ suc n → ⊥
noAbsurd zero p = w p
noAbsurd (suc n) p = noAbsurd n (≡-pred p)
