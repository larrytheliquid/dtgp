module Check where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash

infer : ∀ {n} (t : Term n) (B N : ℕ) → Typed t B N
infer [] B N = well empty
infer (Exec-POP ∷ w ∷ t) B N with infer t B N
... | well p = well (Exec-POP p)
... | ill = ill
-- TODO: analyze
-- infer (Exec-DUP ∷ w ∷ t) B N with infer (w ∷ t) B N
-- with infer-1 w ih B N
-- ... | well p = well (Exec-DUP p)
-- ... | ill = ill
infer (Exec-EQ ∷ w₁ ∷ w₂ ∷ t) B N with infer t (suc B) N
... | well p = well (Exec-EQ p)
... | ill = ill
infer (Exec-K ∷ w₁ ∷ w₂ ∷ t) B N with infer (w₁ ∷ t) B N
... | well p = well (Exec-K p)
... | ill = ill
infer (Exec-SWAP ∷ w₁ ∷ w₂ ∷ t) B N with infer (w₂ ∷ w₁ ∷ t) B N
... | well p = well (Exec-SWAP p)
... | ill = ill
infer (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) B N with infer (w₃ ∷ w₁ ∷ w₂ ∷ t) B N
... | well p = well (Exec-ROT p)
... | ill = ill
-- TODO: analyze
-- infer (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) B N with infer (w₃ ∷ w₃ ∷ w₁ ∷ t) B N
-- ... | ih with infer-1 w₂ ih B N
-- ... | well p = well (Exec-S p)
-- ... | ill = ill
infer (Exec-STACKDEPTH ∷ t) B N with infer t B (suc N)
... | well p = well (Exec-STACKDEPTH p)
... | ill = ill
infer (true ∷ t) B N with infer t (suc B) N
... | well p = well (true p)
... | ill = ill
infer (false ∷ t) B N with infer t (suc B) N
... | well p = well (false p)
... | ill = ill
infer (Bool-POP ∷ t) (suc B) N with infer t B N
... | well p = well (Bool-POP p)
... | ill = ill
infer (AND ∷ t) (suc (suc B)) N with infer t (suc B) N
... | well p = well (AND p)
... | ill = ill
infer (NOT ∷ t) (suc B) N with infer t (suc B) N
... | well p = well (NOT p)
... | ill = ill
infer (Nat-POP ∷ t) B (suc N) with infer t B N
... | well p = well (Nat-POP p)
... | ill = ill
infer (ADD ∷ t) B (suc (suc N)) with infer t B (suc N)
... | well p = well (ADD p)
... | ill = ill
infer (LT ∷ t) B (suc (suc N)) with infer t (suc B) N
... | well p = well (LT p)
... | ill = ill
infer (GT ∷ t) B (suc (suc N)) with infer t (suc B) N
... | well p = well (GT p)
... | ill = ill
infer (nat v ∷ t) B N with infer t B (suc N)
... | well p = well (nat p)
... | ill = ill
infer (_ ∷ _) _ _ = ill

check : ∀ {n} (t : Term n) → Typed t 0 0
check t = infer t 0 0
