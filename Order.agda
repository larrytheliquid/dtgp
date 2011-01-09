module Order where
open import Data.Nat
open import Data.Product

data Econ : ℕ → ℕ → Set where
  []  : Econ 0 0

  greater : ∀ {old-in old-out} →
    (k new-out : ℕ) →
    Econ old-in old-out →
    Econ (suc (old-in + k)) new-out

  less : ∀ {old-in old-out} →
    (k new-out : ℕ) →
    Econ old-in old-out →
    Econ old-in (suc (new-out + k))

  equal : ∀ {old-in old-out} →
    (new-out : ℕ) →
    Econ old-in old-out →
    Econ old-in new-out

append : ∀ {A A' B B'} → Econ B B' → Econ A A' → Econ (A + (B ∸ A')) (B' + (A' ∸ B))
append [] ys = {!!}
append (greater k new-out xs) ys with append xs ys
... | ih = {!!}
append (less k new-out xs) ys = {!!}
append (equal new-out xs) ys = {!!}
