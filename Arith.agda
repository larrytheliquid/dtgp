module Arith where

data Term : Set where
  true false : Term
  if_then_else_ : Term → Term → Term → Term
  zero : Term
  suc pred is-zero : Term → Term

data Numeric : Set where
  zero : Numeric
  suc : Numeric → Numeric

data Value : Set where
  true false : Value
  numeric : Numeric → Value

data Type : Set where
  Bool ℕ : Type

data _∶_ : Term → Type → Set where
  true : true ∶ Bool
  false : false ∶ Bool
  if_then_else_ : ∀ {t₁ t₂ t₃ T} →
    t₁ ∶ Bool → t₂ ∶ T → t₃ ∶ T →
    if t₁ then t₂ else t₃ ∶ T

  zero : zero ∶ ℕ
  suc : ∀ {t} → t ∶ ℕ → suc t ∶ ℕ
  pred : ∀ {t} → t ∶ ℕ → pred t ∶ ℕ
  is-zero : ∀ {t} → t ∶ ℕ → is-zero t ∶ Bool

8-2-3 : if is-zero zero then zero else zero ∶ ℕ
8-2-3 = if is-zero zero then zero else zero
