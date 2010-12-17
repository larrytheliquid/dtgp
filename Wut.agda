module Wut where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils
open import Check

check-split : ∀ {m n} {t : Term (m + n)} → SplitAt m t → Typed t
check-split ([] ++' []) = well empty
check-split ((w ∷ Exec-POP ∷ ws) ++' t) = check-2 (check-split (ws ++' t)) Exec-POP w
check-split ((w ∷ Exec-DUP ∷ ws) ++' t) = check-2 (check-split (ws ++' t)) Exec-DUP w
check-split ((w₂ ∷ w₁ ∷ Exec-EQ ∷ ws) ++' t) = check-3 (check-split (ws ++' t)) Exec-EQ w₁ w₂
check-split ((w₂ ∷ w₁ ∷ Exec-K ∷ ws) ++' t) = check-3 (check-split (ws ++' t)) Exec-K w₁ w₂
check-split ((w₂ ∷ w₁ ∷ Exec-SWAP ∷ ws) ++' t) = check-3 (check-split (ws ++' t)) Exec-SWAP w₁ w₂
check-split ((w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ ws) ++' t) = check-4 (check-split (ws ++' t)) Exec-ROT w₁ w₂ w₃
check-split ((w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ ws) ++' t) = check-4 (check-split (ws ++' t)) Exec-S w₁ w₂ w₃
check-split (ws ++' (Exec-STACKDEPTH ∷ t)) with check-split (ws ++' t)
... | well p = well (Exec-STACKDEPTH ws p)
... | ill = ill
-- check-split {n = n} ([] ++' ys) = check-split ({!!} ++' {!!}) -- check-split (ys ++' [])
check-split .{m = 0} {n = n} ([] ++' ys) rewrite lem-add0 n = check-split {m = n} {n = 0} (ys ++' [])
check-split ((w ∷ ws) ++' t) = check-1 (check-split (ws ++' t)) w

