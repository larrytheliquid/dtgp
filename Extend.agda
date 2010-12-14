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
check-2' (well p) Exec-POP w = well (Exec-POP p)
check-2' p w₁ w₂ = check-1 (check-1 p w₁) w₂

check-2 : ∀ {t} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
check-2 (well p₁) Exec-DUP w with check-2' (well p₁) w w
... | well p₂ = well (Exec-DUP p₁ p₂)
... | ill = ill
check-2 p w₁ w₂ = check-2' p w₁ w₂

check-3 : ∀ {t} → Typed t → (w₁ w₂ w₃ : Word) → Typed (w₃ ∷ w₂ ∷ w₁ ∷ t)
check-3 (well p) Exec-EQ w₁ w₂ = well (Exec-EQ p)
check-3 (well p₁) Exec-SWAP w₁ w₂ with check-2 (well p₁) w₂ w₁
... | well p₂ = well (Exec-SWAP p₁ p₂)
... | ill = ill
check-3 (well p₁) Exec-K w₁ w₂ with check-1 (well p₁) w₁
... | well p₂ = well (Exec-K p₁ p₂)
... | ill = ill
check-3 p w₁ w₂ w₃ = check-1 (check-2 p w₁ w₂) w₃

check-4 : ∀ {t} → Typed t → (w₁ w₂ w₃ w₄ : Word) → Typed (w₄ ∷ w₃ ∷ w₂ ∷ w₁ ∷ t)
check-4 p w₁ w₂ w₃ w₄ = check-1 (check-3 p w₁ w₂ w₃) w₄
