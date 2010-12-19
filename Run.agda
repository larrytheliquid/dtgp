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

data Env {n} (t : Term n) (B N : ℕ) : Set where
  env :
    Vec Bool B →
    Vec ℕ N →
    Env t B N

return-Env : ∀ {n} {t : Term n} → Well t → Set
return-Env {t = t} d with return-type d
... | (B , N) = Env t B N

run : ∀ {n} {t : Term n} (d : Well t) → return-Env d
run empty = env [] []
run (Exec-POP d) = {!!}
run (Exec-DUP d) = {!!}
run (Exec-EQ d) = {!!}
run (Exec-K d) = {!!}
run (Exec-SWAP d) = {!!}
run (Exec-ROT d) = {!!}
run (Exec-S d) = {!!}
run (Exec-STACKDEPTH d) = {!!}
run (true d) = {!!}
run (false d) = {!!}
run (nat d) = {!!}

