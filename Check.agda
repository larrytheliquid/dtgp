module Check where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils

check-1 : ∀ {n} {t : Term n} → Typed t → (w : Word) → Typed (w ∷ t)
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

check-2' : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
check-2' (well p) Exec-POP w = well (Exec-POP p)
check-2' p w₁ w₂ = check-1 (check-1 p w₁) w₂

check-2 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
check-2 (well p₁) Exec-DUP w with check-2' (well p₁) w w
... | well p₂ = well (Exec-DUP p₂)
... | ill = ill
check-2 p w₁ w₂ = check-2' p w₁ w₂

check-3 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ : Word) → Typed (w₃ ∷ w₂ ∷ w₁ ∷ t)
check-3 (well p) Exec-EQ w₁ w₂ = well (Exec-EQ p)
check-3 (well p₁) Exec-SWAP w₁ w₂ with check-2 (well p₁) w₂ w₁
... | well p₂ = well (Exec-SWAP p₂)
... | ill = ill
check-3 (well p₁) Exec-K w₁ w₂ with check-1 (well p₁) w₁
... | well p₂ = well (Exec-K p₂)
... | ill = ill
check-3 p w₁ w₂ w₃ = check-1 (check-2 p w₁ w₂) w₃

check-4' : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ w₄ : Word) → Typed (w₄ ∷ w₃ ∷ w₂ ∷ w₁ ∷ t)
check-4' (well p₁) Exec-ROT w₁ w₂ w₃ with check-3 (well p₁) w₃ w₁ w₂
... | well p₂ = well (Exec-ROT p₂)
... | ill = ill
check-4' p w₁ w₂ w₃ w₄ = check-1 (check-3 p w₁ w₂ w₃) w₄

check-4 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ w₄ : Word) → Typed (w₄ ∷ w₃ ∷ w₂ ∷ w₁ ∷ t)
check-4 (well p₁) Exec-S w₁ w₂ w₃ with check-4' (well p₁) w₁ w₃ w₃ w₂
... | well p₂ = well (Exec-S p₂)
... | ill = ill
check-4 p w₁ w₂ w₃ w₄ = check-4' p w₁ w₂ w₃ w₄

check : ∀ {n} (t : Term n) → Typed t
check [] = well empty
check (w ∷ Exec-DUP ∷ t) = check-2 (check t) Exec-DUP w
check (w₂ ∷ w₁ ∷ Exec-EQ ∷ t) = check-3 (check t) Exec-EQ w₁ w₂
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t) = check-4 (check t) Exec-ROT w₁ w₂ w₃
check (w₂ ∷ w₁ ∷ Exec-SWAP ∷ t) = check-3 (check t) Exec-SWAP w₁ w₂
check (w₂ ∷ w₁ ∷ Exec-K ∷ t) = check-3 (check t) Exec-K w₁ w₂
check (w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t) = check-4 (check t) Exec-S w₁ w₂ w₃
check (w ∷ Exec-POP ∷ t) = check-2 (check t) Exec-POP w
check {n = suc m} t rewrite lem-add1 m with splitAt m {1} t
check {suc _} ._ | xs ++' (Exec-STACKDEPTH ∷ []) with check xs
... | wut = {!!}
check {suc _} ._ | xs ++' ys with check xs -- but not ys!
... | lul = {!!}
-- check (w ∷ t) = check-1 (check t) w

-- xs ++' (Exec-STACKDEPTH ∷ ys)
-- check-n (check ys) Exec-STACKDEPTH xs
