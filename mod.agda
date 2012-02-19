module mod where

open import Data.Nat as N using (ℕ ; _≤′_ ; _<′_)
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary
open import Induction.Nat
open import Data.Product
open import Data.Empty using (⊥-elim)

z≤′ : ∀ {n} → N.zero ≤′ n
z≤′ {N.zero} = N.≤′-refl
z≤′ {N.suc n} = N.≤′-step z≤′

s≤′s : ∀ {m n} → (m ≤′ n) → N.suc m ≤′ N.suc n
s≤′s N.≤′-refl = N.≤′-refl
s≤′s (N.≤′-step m≤′n) = N.≤′-step (s≤′s m≤′n)

p≤′p : ∀ {m n} → (N.suc m ≤′ N.suc n) → m ≤′ n
p≤′p N.≤′-refl = N.≤′-refl
p≤′p {m} {N.zero} (N.≤′-step ())
p≤′p {m} {N.suc n} (N.≤′-step m≤′n) = N.≤′-step (p≤′p m≤′n)

¬≤′ : ∀ {m n} → ¬ (m ≤′ n) → n <′ m
¬≤′ {N.zero} ¬p = ⊥-elim (¬p z≤′)
¬≤′ {N.suc m} {N.zero} ¬p = s≤′s z≤′
¬≤′ {N.suc m} {N.suc n} ¬p = s≤′s (¬≤′ {m} {n} (λ w → ¬p (s≤′s w)))

_≤′?_ : (m n : ℕ) → Dec (m ≤′ n)
N.zero ≤′? N.zero = yes N.≤′-refl
N.zero ≤′? N.suc n = yes z≤′
N.suc m ≤′? N.zero = no (λ ())
N.suc m ≤′? N.suc n with m ≤′? n
N.suc m ≤′? N.suc n | yes m≤′n = yes (s≤′s m≤′n)
N.suc m ≤′? N.suc n | no ¬p = no (λ w → ¬p (p≤′p w))

_<′?_ : (m n : ℕ) → Dec (m <′ n)
m <′? n = N.suc m ≤′? n

diff1 : ∀ m n → m <′ n → ∃ λ v → v <′ n
diff1 m .(N.suc m) N.≤′-refl = N.zero , s≤′s z≤′
diff1 m .(N.suc n) (N.≤′-step {n} m≤′n) with diff1 m n m≤′n
diff1 m .(N.suc n) (N.≤′-step {n} m≤′n) | d , d<′n = N.suc d , s≤′s d<′n

fromℕ<′ : ∀ {n} m → m <′ n → Fin n
fromℕ<′ m N.≤′-refl = fromℕ m
fromℕ<′ m (N.≤′-step m≤′n) = inject₁ (fromℕ<′ m m≤′n)

mod : ∀ n → ℕ → Fin (N.suc n)
mod n i = <-rec (λ _ → Fin (N.suc n)) go i
  where
    go : (x : ℕ) → ((y : ℕ) → y <′ x → Fin (N.suc n)) → Fin (N.suc n)
    go x f with n <′? x
    go x f | yes p with diff1 n x p
    go x f | yes p | d , d<′x = f d d<′x
    go x f | no ¬p = fromℕ<′ x (¬≤′ ¬p)

max : ∀ {n} → Fin (N.suc n)
max {N.zero} = zero
max {N.suc n} = suc max

invert : ∀ {n} → Fin n → Fin n
invert {N.zero} ()
invert {N.suc n} zero = fromℕ n
invert {N.suc n} (suc i) = inject₁ (invert i)

_<?_ : ∀ {n} → Decidable {A = Fin n} _<_
zero <? zero = no (λ ())
zero <? suc i = yes (N.s≤s N.z≤n)
suc i <? zero = no (λ ())
suc i <? suc j with i <? j
suc i <? suc j | yes p = yes (N.s≤s p)
suc i <? suc j | no ¬p = no helper
  where helper : ¬ (suc i < suc j)
        helper (N.s≤s i≤j) = ¬p i≤j

msuc : ∀ {n} → Fin n → Fin n
msuc {N.zero} ()
msuc {N.suc n} i with i <? max
msuc {N.suc N.zero} i | yes ()
msuc {N.suc (N.suc n)} zero | yes (N.s≤s m≤n) = suc zero
msuc {N.suc (N.suc n)} (suc i) | yes (N.s≤s m≤n) = suc (msuc i)
msuc {N.suc n} i | no ¬p = zero

mpred : ∀ {n} → Fin n → Fin n
mpred i = invert (msuc (invert i))

{-
mplus : ∀ {m n} → Fin m → Fin n → Fin n
mplus zero j = ?
mplus (suc i) j = ?
-}