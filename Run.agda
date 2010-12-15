module Run where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Vec
open import Stash

_lt_ : ℕ → ℕ → Bool
zero lt (suc n) = true
(suc n) lt (suc m) = n lt m
_ lt _ = false

_gt_ : ℕ → ℕ → Bool
(suc n) gt zero = true
(suc n) gt (suc m) = n gt m
_ gt _ = false

data Env (t : Term) (B N : ℕ) : Set where
  env :
    Vec Bool B →
    Vec ℕ N →
    Env t B N

run : ∀ {B N t} →
  Well {B} {N} t → Env t B N
run empty = env [] []
run (Exec-DUP _ d) with run d
... | env bs ns = env bs ns
-- TODO: equality for terms/bools/nats
run (Exec-EQ d) with run d
... | env bs ns = env (false ∷ bs) ns
run (Exec-ROT _ d) with run d
... | env bs ns = env bs ns
run (Exec-SWAP _ d) with run d
... | env bs ns = env bs ns
run (Exec-K _ d) with run d
... | env bs ns = env bs ns
run (Exec-S _ d) with run d
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
run (nat {n = n} d) with run d
... | env bs ns = env bs (n ∷ ns)
run (Nat-POP d) with run d
... | env bs (_ ∷ ns) = env bs ns
run (ADD d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env bs (n₁ + n₂ ∷ ns)
run (LT d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env (n₁ lt n₂ ∷ bs) ns
run (GT d) with run d
... | env bs (n₂ ∷ n₁ ∷ ns) = env (n₁ gt n₂ ∷ bs) ns

