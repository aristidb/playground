module negneg where

open import Data.Empty
open import Relation.Nullary

test : {A : Set} → A → ¬ ¬ A
test x w = w x

neg2 : {A : Set} → ¬ ¬ ¬ ¬ A → ¬ ¬ A
neg2 p w = p (λ z → z w)
