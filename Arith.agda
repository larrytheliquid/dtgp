module Arith where
open import Data.Product
open import Relation.Binary.PropositionalEquality

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

inversion-1 : ∀ {T} → true ∶ T → T ≡ Bool
inversion-1 true = refl

inversion-2 : ∀ {T} → false ∶ T → T ≡ Bool
inversion-2 false = refl

inversion-3 : ∀ {t₁ t₂ t₃ T} →
  if t₁ then t₂ else t₃ ∶ T → t₁ ∶ Bool × t₂ ∶ T × t₃ ∶ T
inversion-3 (if true then t else t') = true , t , t'
inversion-3 (if false then t else t') = false , t , t'
inversion-3 (if (if b then t else t') then u else u') =
  if b then t else t' , u , u'
inversion-3 (if is-zero n then t else t') =
  is-zero n , t , t'

inversion-4 : ∀ {T} → zero ∶ T → T ≡ ℕ
inversion-4 zero = refl

inversion-5 : ∀ {t T} → suc t ∶ T → T ≡ ℕ × t ∶ ℕ
inversion-5 (suc n) = refl , n

inversion-6 : ∀ {t T} → pred t ∶ T → T ≡ ℕ × t ∶ ℕ
inversion-6 (pred n) = refl , n

inversion-7 : ∀ {t T} → is-zero t ∶ T → T ≡ Bool × t ∶ ℕ
inversion-7 (is-zero n) = refl , n
