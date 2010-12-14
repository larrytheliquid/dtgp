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
check (w ∷ Exec-DUP ∷ t) = ill -- TODO2=
check (Exec-DUP ∷ t) = ill
check (_ ∷ _ ∷ Exec-EQ ∷ t) with check t
... | well p = well (Exec-EQ p)
... | ill = ill
check (Exec-EQ ∷ t) = ill
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t) = ill -- TODO3
check (Exec-ROT ∷ t) = ill
check (w₂ ∷ w₁ ∷ Exec-SWAP ∷ t) = ill -- TODO2
check (Exec-SWAP ∷ t) = ill
check (w₂ ∷ w₁ ∷ Exec-K ∷ t) with check t
... | ill = ill
... | well p₁ with check-1 (well p₁) w₁
... | ill = ill
... | well p₂ = well (Exec-K p₁ p₂)
check (Exec-K ∷ t) = ill
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t) = ill -- TODO4
check (Exec-S ∷ t) = ill
check (_ ∷ Exec-POP ∷ t) with check t
... | well p = well (Exec-POP p)
... | _ = ill
check (Exec-POP ∷ t) = ill
check (w ∷ t) = check-1 (check t) w
