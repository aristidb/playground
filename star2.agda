module star2 where

open import Data.Star
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Function.Inverse

data Suc : ℕ -> ℕ -> Set where
  suc! : ∀ {n} -> Suc n (suc n)

next : Suc =[ suc ]⇒ Suc
next {n} suc! = suc!

Suc* : ℕ -> ℕ -> Set
Suc* = Star Suc

next* : ∀ {n m} -> Suc* n m -> Suc* (suc n) (suc m)
next* = gmap suc next

prev* : ∀ {n m} -> Suc* (suc n) (suc m) -> Suc* n m
prev* ε = ε
prev* (suc! ◅ xs) = suc! ◅ prev* xs

Suc0* : ∀ {m} -> Suc* 0 m
Suc0* {zero} = ε
Suc0* {suc m} = suc! ◅ next* (Suc0* {m})

LE : ℕ -> ℕ -> Set
LE zero m = ⊤
LE (suc n) zero = ⊥
LE (suc n) (suc m) = LE n m

LE-refl : Reflexive LE
LE-refl {zero} = tt
LE-refl {suc n} = LE-refl {n}

LE◅ : ∀ {n m} -> LE (suc n) m -> LE n m
LE◅ {zero} x = tt
LE◅ {suc n} {zero} ()
LE◅ {suc n} {suc m} x = LE◅ {n} {m} x

LE->Suc* : ∀ {n m} -> LE n m -> Suc* n m
LE->Suc* {zero} tt = Suc0*
LE->Suc* {suc n} {zero} ()
LE->Suc* {suc n} {suc m} x = next* (LE->Suc* x)

Suc*->LE : ∀ {n m} -> Suc* n m -> LE n m
Suc*->LE {zero} x = tt
Suc*->LE {suc n} ε = LE-refl {suc n}
Suc*->LE {suc n} {m} (suc! ◅ xs) = LE◅ {suc n} {m} (Suc*->LE xs)

Suc*-asym : ∀ {n m} -> Suc* n m -> ¬ (Suc* (suc m) n)
Suc*-asym {zero} w p = Suc*->LE p
Suc*-asym {suc n} {zero} w p = Suc*->LE w
Suc*-asym {suc .m} {suc m} ε (suc! ◅ xs) = {!Suc*-asym {m} {m} ε!}
Suc*-asym {suc n} {suc m} (suc! ◅ xs) p = {!!}

LE->Suc*->LE : ∀ {n m} x -> LE->Suc* {n} {m} (Suc*->LE {n} {m} x) ≡ x
LE->Suc*->LE {n} {m} x with LE->Suc* {n} {m} (Suc*->LE {n} {m} x)
LE->Suc*->LE ε | ε = refl
LE->Suc*->LE (suc! ◅ xs) | ε = {!!}
LE->Suc*->LE ε | x' ◅ xs = {!!}
LE->Suc*->LE (x ◅ xs) | x' ◅ xs' = {!!}

Suc*↔LE : ∀ {n m} -> Suc* n m ↔ LE n m
Suc*↔LE {n} {m} = record {
                    to = record { _⟨$⟩_ = Suc*->LE; cong = cong _ };
                    from = record { _⟨$⟩_ = LE->Suc* {n} {m}; cong = cong _ };
                    inverse-of = record { left-inverse-of = {!!}; right-inverse-of = {!!} } }