module Another where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils
open import Check

ona : ∀ {n} (t : Term n) → Typed t
ona [] = well empty
ona (Exec-POP ∷ w ∷ t) = check-2 (ona t) w Exec-POP
ona (Exec-DUP ∷ w ∷ t) = check-2 (ona t) w Exec-DUP
ona (Exec-EQ ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-EQ
ona (Exec-K ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-K
ona (Exec-SWAP ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-SWAP
ona (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) = check-4 (check t) w₃ w₂ w₁ Exec-ROT
ona (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) = check-4 (check t) w₃ w₂ w₁ Exec-S
ona (Exec-STACKDEPTH ∷ t) with ona t
... | well p = well (Exec-STACKDEPTH [] p)
... | ill = ill
ona (w ∷ t) = check-1 (check t) w
