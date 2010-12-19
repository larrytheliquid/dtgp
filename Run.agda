module Run where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Product
open import Stash
open import Utils

return-type : ∀ {n B N} {t : Term n} → t ∶ B ∣ N → ℕ × ℕ
return-type (empty {B = B} {N = N}) = B , N
return-type (Exec-POP d) = return-type d
return-type (Exec-DUP d) = return-type d
return-type (Exec-EQ d) = return-type d
return-type (Exec-K d) = return-type d
return-type (Exec-SWAP d) = return-type d
return-type (Exec-ROT d) = return-type d
return-type (Exec-S d) = return-type d
return-type (Exec-STACKDEPTH d) = return-type d
return-type (true d) = return-type d
return-type (false d) = return-type d
return-type (Bool-POP d) = return-type d
return-type (AND d) = return-type d
return-type (NOT d) = return-type d
return-type (nat d) = return-type d
return-type (Nat-POP d) = return-type d
return-type (ADD d) = return-type d
return-type (LT d) = return-type d
return-type (GT d) = return-type d

data Env {n B N} {t : Term n} (d : t ∶ B ∣ N) (B' N' : ℕ) : Set where
  env :
    Vec Bool B' →
    Vec ℕ N' →
    Env d B' N'

return-Env : ∀ {n B N} {t : Term n} → t ∶ B ∣ N → Set
return-Env d with return-type d
... | (B , N) = Env d B N

run : ∀ {n B N} {t : Term n} (d : t ∶ B ∣ N) → return-Env d
run empty = {!!}
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
run (Bool-POP y) = {!!}
run (AND y) = {!!}
run (NOT y) = {!!}
run (nat y) = {!!}
run (Nat-POP y) = {!!}
run (ADD y) = {!!}
run (LT y) = {!!}
run (GT y) = {!!}

