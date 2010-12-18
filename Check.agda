module Check where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash

check' : ∀ {n} {t : Term n} → (w : Word) → Typed t → Typed (w ∷ t)
check' true (well {B = suc _} p) = well (true p)
check' false (well {B = suc _} p) = well (false p)
check' Bool-POP (well p) = well (Bool-POP p)
check' AND (well {B = suc _} p) = well (AND p)
check' NOT (well {B = suc _} p) = well (NOT p)
check' Nat-POP (well p) = well (Nat-POP p)
check' ADD (well {N = suc _} p) = well (ADD p)
check' LT (well {B = suc _} p) = well (LT p)
check' GT (well {B = suc _} p) = well (GT p)
check' (nat v) (well {N = suc _} p) = well (nat p)
check' _ _ = ill

check : ∀ {n} (t : Term n) → Typed t
-- TODO: need B ∣ N
check [] = well {B = 0} {N = 0} empty
check (Exec-POP ∷ w ∷ E) with check E
... | well p = well (Exec-POP p)
... | ill = ill
-- TODO: analyze
check (Exec-DUP ∷ w ∷ E) with check (w ∷ E)
... | ih with check' w ih
... | well p = well (Exec-DUP p)
... | ill = ill
check (Exec-EQ ∷ w₁ ∷ w₂ ∷ E) with check E
... | well {B = suc _} p = well (Exec-EQ p)
... | well {B = zero} p = ill
... | ill = ill
check (Exec-K ∷ w₁ ∷ w₂ ∷ E) with check (w₁ ∷ E)
... | well p = well (Exec-K p)
... | ill = ill
check (Exec-SWAP ∷ w₁ ∷ w₂ ∷ E) with check (w₂ ∷ w₁ ∷ E)
... | well p = well (Exec-SWAP p)
... | ill = ill
check (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ E) with check (w₃ ∷ w₁ ∷ w₂ ∷ E)
... | well p = well (Exec-ROT p)
... | ill = ill
-- TODO: analyze
check (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ E) with check (w₃ ∷ w₃ ∷ w₁ ∷ E)
... | ih with check' w₂ ih
... | well p = well (Exec-S p)
... | ill = ill
check (Exec-STACKDEPTH ∷ E) with check E
... | well {N = suc _} p = well (Exec-STACKDEPTH p)
... | well {N = zero} p = ill
... | ill = ill
check (w ∷ E) = check' w (check E)

