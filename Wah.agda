open import Data.Nat hiding (_∸_)
module Wah (W : Set) (In Out : W → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero  ∸ n = zero
m     ∸ zero  = m
suc m ∸ suc n = m ∸ n

min0 : ∀ n → n ∸ 0 ≡ n
min0 zero = refl
min0 (suc n) with min0 n
... | p rewrite p = refl

plus0 : ∀ n → n + 0 ≡ n
plus0 zero = refl
plus0 (suc n) with plus0 n
... | p rewrite p = refl

add-assoc : ∀ m n o → m + (n + o) ≡ m + n + o
add-assoc zero n o = refl
add-assoc (suc m) n o with add-assoc m n o
... | p rewrite p = refl

addr : ∀ m n → m + suc n ≡ suc m + n
addr zero n = refl
addr (suc m) n with addr m n
... | p rewrite p = refl

add-comm : ∀ m n → m + n ≡ n + m
add-comm zero n rewrite plus0 n = refl
add-comm (suc m) n
  rewrite addr n m
  with add-comm m n
... | p rewrite p = refl

addl : ∀ m n → suc (m + n) ≡ m + suc n
addl zero n = refl
addl (suc m) n with addl m n
... | p rewrite p = refl

lem1 : ∀ B B' B0 B1 Inx →
  Inx ∸ (B' ∸ B0 + B1) + (B0 ∸ B' + B)
  ≡
  Inx ∸ B1 + B0 ∸ B' + B
lem1 B zero B0 B1 Inx
  rewrite
    min0 B0
  | min0 (Inx ∸ B1 + B0)
  | add-assoc (Inx ∸ B1) B0 B
  = refl
lem1 B (suc B') zero B1 zero = refl
lem1 B (suc B') zero zero (suc Inx)
  rewrite
    plus0 B'
  | plus0 Inx
  = refl
lem1 B (suc B') zero (suc B1) (suc Inx)
  rewrite
    plus0 (Inx ∸ B1)
  | add-comm B' (suc B1)
  | addl B1 B'
  | add-assoc Inx B1 (suc B')
  = {!!}
lem1 B (suc B') (suc B0) B1 Inx = {!!}

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _∷_ : ∀ {B B'} →
    (w : W) →
    B ⟶ B' →
    (In w ∸ B') + B ⟶ (B' ∸ In w) + Out w

_++_ : ∀ {B B' C C'} →
  C ⟶ C' →
  B ⟶ B' →
  (C ∸ B') + B ⟶ (B' ∸ C) + C'
[] ++ ys = {!!}
(x ∷ xs) ++ ys with xs ++ ys
... | ih with x ∷ ih
... | ret = {!!}
