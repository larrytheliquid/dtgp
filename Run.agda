module Run where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Product
open import Stash
open import Utils

data Env {n} (t : Term n) (B N : ℕ) : Set where
  env :
    Vec Bool B →
    Vec ℕ N →
    Env t B N

run : ∀ {n Bool Nat} {t : Term n} →
  Bool ∣ Nat ⊢ t ∶ 0 ∣ 0 → Env t Bool Nat
run empty = env [] []
run (Exec-POP y) = {!!}
run (Exec-DUP y) = {!!}
run (Exec-EQ y) = {!!}
run (Exec-K y) = {!!}
run (Exec-SWAP y) = {!!}
run (Exec-ROT y) = {!!}
run (Exec-S y) = {!!}
run (Exec-STACKDEPTH y) = {!!}
run (true y) = {!!}
run (false y) = {!!}
run (nat y) = {!!}
