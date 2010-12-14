module Check where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Stash
open import Extend

check : (t : Term) → Typed t
check [] = well empty
check (w ∷ Exec-DUP ∷ t) = check-2 (check t) Exec-DUP w
check (w₂ ∷ w₁ ∷ Exec-EQ ∷ t) = check-3 (check t) Exec-EQ w₁ w₂
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t) = ill -- TODO4
check (w₂ ∷ w₁ ∷ Exec-SWAP ∷ t) = check-3 (check t) Exec-SWAP w₁ w₂
check (w₂ ∷ w₁ ∷ Exec-K ∷ t) = check-3 (check t) Exec-K w₁ w₂
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t) = ill -- TODO4
check (w ∷ Exec-POP ∷ t) = check-2 (check t) Exec-POP w
check (w ∷ t) = check-1 (check t) w
