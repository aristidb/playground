module cmp where

open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

compare-equal : ∀ n → compare n n ≡ equal n
compare-equal zero = refl
compare-equal (suc n) with compare n n | compare-equal n
compare-equal (suc n) | .(equal n) | refl = refl

