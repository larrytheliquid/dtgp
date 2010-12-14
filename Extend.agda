module Extend where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Stash

check-1 : ∀ {t} → Typed t → (w : Word) → Typed (w ∷ t)
check-1 (well p) true = well (true p)
check-1 (well p) false = well (false p)
check-1 (well {B = suc (suc _)} p) Bool-POP = well (Bool-POP p)
check-1 (well {B = suc (suc _)} p) AND = well (AND p)
check-1 (well {B = suc _} p) NOT = well (NOT p)
check-1 (well {N = suc (suc _)} p) Nat-POP = well (Nat-POP p)
check-1 (well {N = suc (suc _)} p) ADD = well (ADD p)
check-1 (well {N = suc (suc _)} p) LT = well (LT p)
check-1 (well {N = suc (suc _)} p) GT = well (GT p)
check-1 (well p) (nat _) = well (nat p)
check-1 _ _ = ill

check-2' : ∀ {t} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
check-2' (well p) Exec-POP w₂ = well (Exec-POP p)
check-2' ill Exec-POP w₂ = ill
check-2' p w₁ w₂ = check-1 (check-1 p w₁) w₂

check-2 : ∀ {t} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
check-2 (well p₁) Exec-DUP w₂ with check-2' (well p₁) w₂ w₂
... | well p₂ = well (Exec-DUP p₁ p₂)
... | ill = ill
check-2 ill Exec-DUP w₂ = ill
check-2 p w₁ w₂ = check-2' p w₁ w₂

check-3 : ∀ {t} → Typed t → (w₁ w₂ w₃ : Word) → Typed (w₃ ∷ w₂ ∷ w₁ ∷ t)
check-3 (well p₁) Exec-SWAP w₂ w₃ with check-2 (well p₁) w₃ w₂
... | well p₂ = well (Exec-SWAP p₁ p₂)
... | ill = ill
check-3 ill Exec-SWAP w₂ w₃ = ill
check-3 p w₁ w₂ w₃ = check-1 (check-2 p w₁ w₂) w₃
