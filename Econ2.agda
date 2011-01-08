module Econ2 where
open import Data.Nat
open import Data.Product

In : ℕ → ℕ → ℕ → ℕ
In B B' A = B + (A ∸ B')

Out : ℕ → ℕ → ℕ → ℕ
Out B' A A' = A' + (B' ∸ A)

data Econ : ℕ → ℕ → Set where
  []  : Econ 0 0
  cons : ∀ {A A'} →
    (B B' : ℕ) →
    Econ A A' →
    Econ (In B B' A) (Out B' A A')

In-Econ : ∀ {B B' A A'} → Econ B B' → Econ A A' → ℕ
In-Econ {A = A} [] ys = A
In-Econ (cons B B' xs) ys = In B B' (In-Econ xs ys)

Out-Econ : ∀ {B B' A A'} → Econ B B' → Econ A A' → ℕ
Out-Econ {A' = A'} [] ys = A'
Out-Econ (cons B B' xs) ys =
  Out B' (In-Econ xs ys) (Out-Econ xs ys)

append : ∀ {B B' A A'} → (xs : Econ B B') → (ys : Econ A A') →
  Econ (In-Econ xs ys) (Out-Econ xs ys)
append [] ys = ys
append (cons B B' xs) ys = cons B B' (append xs ys)



