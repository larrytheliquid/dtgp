module Check where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Stash

check : (t : Term) → Typed t
check [] = well empty
check (w ∷ Exec-DUP ∷ t) = ill -- TODO
check (Exec-DUP ∷ t) = ill
check (_ ∷ _ ∷ Exec-EQ ∷ t) with check t
... | well p = well (Exec-EQ p)
... | _ = ill
check (Exec-EQ ∷ t) = ill
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t) = ill -- TODO
check (Exec-ROT ∷ t) = ill
check (w₂ ∷ w₁ ∷ Exec-SWAP ∷ t) = ill -- TODO
check (Exec-SWAP ∷ t) = ill
check (w₂ ∷ w₁ ∷ Exec-K ∷ t) = ill -- TODO
check (Exec-K ∷ t) = ill
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t) = ill -- TODO
check (Exec-S ∷ t) = ill
check (_ ∷ Exec-POP ∷ t) with check t
... | well p = well (Exec-POP p)
... | _ = ill
check (Exec-POP ∷ t) = ill
check (true ∷ t) with check t
... | well p = well (true p)
... | _ = ill
check (false ∷ t) with check t
... | well p = well (false p)
... | _ = ill
check (Bool-POP ∷ t) with check t
... | well {B = suc _} p = well (Bool-POP p)
... | _ = ill
check (AND ∷ t) with check t
... | well {B = suc (suc _)} p = well (AND p)
... | _ = ill
check (NOT ∷ t) with check t
... | well {B = suc _} p = well (NOT p)
... | _ = ill
check (Nat-POP ∷ t) with check t
... | well {N = suc _} p = well (Nat-POP p)
... | _ = ill
check (ADD ∷ t) with check t
... | well {N = suc (suc _)} p = well (ADD p)
... | _ = ill
check (LT ∷ t) with check t
... | well {N = suc (suc _)} p = well (LT p)
... | _ = ill
check (GT ∷ t) with check t
... | well {N = suc (suc _)} p = well (GT p)
... | _ = ill
check (nat _ ∷ t) with check t
... | well p = well (nat p)
... | _ = ill


