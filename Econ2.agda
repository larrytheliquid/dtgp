module Econ2 where
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

In : ℕ → ℕ → ℕ → ℕ
In new-in old-in old-out =
  (new-in ∸ old-out) + old-in

Out : ℕ → ℕ → ℕ → ℕ
Out new-out new-in old-out =
  (old-out ∸ new-in) + new-out

lem-minus : ∀ n → n ∸ n ≡ 0
lem-minus zero = refl
lem-minus (suc n) = lem-minus n

In-Trans : ∀ old-out old-in →
  In old-out old-in old-out ≡ old-in
In-Trans old-out old-in
  rewrite lem-minus old-out = refl

Out-Trans : ∀ new-out old-out →
  Out new-out old-out old-out ≡ new-out
Out-Trans new-out old-out
  rewrite lem-minus old-out = refl

data Econ : ℕ → ℕ → Set where
  []  : Econ 0 0
  cons : ∀ {old-in old-out} →
    (new-in new-out : ℕ) →
    Econ old-in old-out →
    Econ (In new-in old-in old-out) 
         (Out new-out new-in old-out)

Out-Econ : ∀ {B B' A A'} → Econ B B' → Econ A A' → ℕ
Out-Econ {A' = A'} [] ys = A'
Out-Econ (cons B B' xs) ys =
  Out B' B (Out-Econ xs ys)

In-Econ : ∀ {B B' A A'} → Econ B B' → Econ A A' → ℕ
In-Econ {A = A} [] ys = A
In-Econ (cons B B' xs) ys = In B (In-Econ xs ys) (Out-Econ xs ys)

Out-Assoc : ∀ {B B' A A'} →
  (xs : Econ B B') →
  (ys : Econ A A') →
  Out-Econ xs ys ≡ Out B' B A'
Out-Assoc [] ys = {!!}
Out-Assoc (cons {old-in} {old-out} new-in new-out xs) ys with Out-Assoc xs ys
... | ih rewrite ih with new-in | old-out
... | m | zero  = {!!}
... | zero | suc n  = {!!}
... | suc m | suc n  = {!!}

append : ∀ {B B' A A'} → (xs : Econ B B') → (ys : Econ A A') →
  Econ (In-Econ xs ys) (Out-Econ xs ys)
append [] ys = ys
append (cons B B' xs) ys = cons B B' (append xs ys)


