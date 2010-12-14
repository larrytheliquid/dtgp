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
