module Run where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Vec
open import Stash
open import Utils

data Env : Set where
  env : ∀ {n B N} {t : Term n} →
    t ∶ B ∣ N →
    List Bool →
    List ℕ →
    Env

run' : Env → Env
run' (env {B = B} {N = N} {t = []} empty bs ns) =
  env {B = B} {N = N} {t = []} empty bs ns
run' (env (Exec-POP d) bs ns) = run' (env d bs ns)
run' (env (Exec-DUP d) bs ns) = run' (env d bs ns)
run' (env (Exec-EQ {w₁ = w₁} {w₂ = w₂} d) bs ns) =
  run' (env d (eq-Word w₂ w₁ ∷ bs) ns)
run' (env (Exec-K d) bs ns) = run' (env d bs ns)
run' (env (Exec-SWAP d) bs ns) = run' (env d bs ns)
run' (env (Exec-ROT d) bs ns) = run' (env d bs ns)
run' (env (Exec-S d) bs ns) = run' (env d bs ns)
run' (env (Exec-STACKDEPTH {n = n} d) bs ns) =
  run' (env d bs (n ∷ ns))
run' (env (true d) bs ns) =
  run' (env d (true ∷ bs) ns)
run' (env (false d) bs ns) =
  run' (env d (false ∷ bs) ns)
run' (env (Bool-POP d) (b ∷ bs) ns) =
  run' (env d bs ns)
run' (env (Bool-POP d) bs ns) = run' (env d bs ns)
run' (env (AND d) (b₁ ∷ b₂ ∷ bs) ns) =
  run' (env d (b₂ ∧ b₁ ∷ bs) ns)
run' (env (AND d) bs ns) = run' (env d bs ns)
run' (env (NOT d) (b ∷ bs) ns) =
  run' (env d (not b ∷ bs) ns)
run' (env (NOT d) bs ns) = run' (env d bs ns)
run' (env (nat {v = v} d) bs ns) = run' (env d bs (v ∷ ns))
run' (env (Nat-POP d) bs ns) = run' (env d bs ns)
run' (env (ADD d) bs (n₁ ∷ n₂ ∷ ns)) =
  run' (env d bs (n₂ + n₁ ∷ ns))
run' (env (ADD d) bs ns) = run' (env d bs ns)
run' (env (LT d) bs (n₁ ∷ n₂ ∷ ns)) =
  run' (env d (n₂ lt n₁ ∷ bs) ns)
run' (env (LT d) bs ns) = run' (env d bs ns)
run' (env (GT d) bs (n₁ ∷ n₂ ∷ ns)) =
  run' (env d (n₂ gt n₁ ∷ bs) ns)
run' (env (GT d) bs ns) = run' (env d bs ns)

run : ∀ {n} {t : Term n} →
    Well t → Env
run d = run' (env d [] [])
