module Check where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash

check' : ∀ {n} (t : Term n) (B N : ℕ) → Typed t B N
check' [] B N = well empty
check' (Exec-POP ∷ w ∷ t) B N with check' t B N
... | well p = well (Exec-POP p)
... | ill = ill
-- TODO: analyze
-- check' (Exec-DUP ∷ w ∷ t) B N with check' (w ∷ t) B N
-- with check'-1 w ih B N
-- ... | well p = well (Exec-DUP p)
-- ... | ill = ill
check' (Exec-EQ ∷ w₁ ∷ w₂ ∷ t) B N with check' t (suc B) N
... | well p = well (Exec-EQ p)
... | ill = ill
check' (Exec-K ∷ w₁ ∷ w₂ ∷ t) B N with check' (w₁ ∷ t) B N
... | well p = well (Exec-K p)
... | ill = ill
check' (Exec-SWAP ∷ w₁ ∷ w₂ ∷ t) B N with check' (w₂ ∷ w₁ ∷ t) B N
... | well p = well (Exec-SWAP p)
... | ill = ill
check' (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) B N with check' (w₃ ∷ w₁ ∷ w₂ ∷ t) B N
... | well p = well (Exec-ROT p)
... | ill = ill
-- TODO: analyze
-- check' (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) B N with check' (w₃ ∷ w₃ ∷ w₁ ∷ t) B N
-- ... | ih with check'-1 w₂ ih B N
-- ... | well p = well (Exec-S p)
-- ... | ill = ill
check' (Exec-STACKDEPTH ∷ t) B N with check' t B (suc N)
... | well p = well (Exec-STACKDEPTH p)
... | ill = ill
check' (true ∷ t) B N with check' t (suc B) N
... | well p = well (true p)
... | ill = ill
check' (false ∷ t) B N with check' t (suc B) N
... | well p = well (false p)
... | ill = ill
check' (Bool-POP ∷ t) (suc B) N with check' t B N
... | well p = well (Bool-POP p)
... | ill = ill
check' (AND ∷ t) (suc (suc B)) N with check' t (suc B) N
... | well p = well (AND p)
... | ill = ill
check' (NOT ∷ t) (suc B) N with check' t (suc B) N
... | well p = well (NOT p)
... | ill = ill
check' (Nat-POP ∷ t) B (suc N) with check' t B N
... | well p = well (Nat-POP p)
... | ill = ill
check' (ADD ∷ t) B (suc (suc N)) with check' t B (suc N)
... | well p = well (ADD p)
... | ill = ill
check' (LT ∷ t) B (suc (suc N)) with check' t (suc B) N
... | well p = well (LT p)
... | ill = ill
check' (GT ∷ t) B (suc (suc N)) with check' t (suc B) N
... | well p = well (GT p)
... | ill = ill
check' (nat v ∷ t) B N with check' t B (suc N)
... | well p = well (nat p)
... | ill = ill
check' (_ ∷ _) _ _ = ill

check : ∀ {n} (t : Term n) → Typed t 0 0
check t = check' t 0 0
