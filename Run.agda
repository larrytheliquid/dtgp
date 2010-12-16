module Run where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils

data Env {n} (t : Term n) (B N : ℕ) : Set where
  env :
    Vec Bool B →
    Vec ℕ N →
    Env t B N

run : ∀ {n B N} {t : Term n} →
  Well {B = B} {N = N} t → Env t B N
run empty = env [] []
run (Exec-STACKDEPTH {n₂ = n₂} t₂ d) with run d
... | env bs ns = env bs (n₂ ∷ ns)
run (Exec-DUP d) with run d
... | env bs ns = env bs ns
run (Exec-EQ {w₁ = w₁} {w₂ = w₂} d) with run d
... | env bs ns = env (eq-Word w₁ w₂ ∷ bs) ns
run (Exec-ROT d) with run d
... | env bs ns = env bs ns
run (Exec-SWAP d) with run d
... | env bs ns = env bs ns
run (Exec-K d) with run d
... | env bs ns = env bs ns
run (Exec-S d) with run d
... | env bs ns = env bs ns
run (Exec-POP d) with run d
... | env bs ns = env bs ns
run (true d) with run d
... | env bs ns = env (true ∷ bs) ns
run (false d) with run d
... | env bs ns = env (false ∷ bs) ns
run (Bool-POP d) with run d
... | env (_ ∷ bs) ns = env bs ns
run (AND d) with run d
... | env (b₂ ∷ b₁ ∷ bs) ns = env (b₁ ∧ b₂ ∷ bs) ns
run (NOT d) with run d
... | env (b ∷ bs) ns = env (not b ∷ bs) ns
run (nat {v = v} d) with run d
... | env bs ns = env bs (v ∷ ns)
run (Nat-POP d) with run d
... | env bs (_ ∷ ns) = env bs ns
run (ADD d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env bs (n₁ + n₂ ∷ ns)
run (LT d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env (n₁ lt n₂ ∷ bs) ns
run (GT d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env (n₁ gt n₂ ∷ bs) ns

