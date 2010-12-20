module Direct where
open import Data.Nat
open import Data.Bool
open import Data.Vec

data _∣_⟶_∣_ :
  (Exec-EQ : ℕ) (Bool : ℕ)
  (Exec-EQ : ℕ) (Bool : ℕ)
  → Set where

  NOOP     : ∀ {E B} →      E  ∣      B  ⟶      E  ∣      B
  Exec-EQ  : ∀ {E B} → (2 + E) ∣      B  ⟶      E  ∣ (1 + B)
  Exec-K   : ∀ {E B} → (2 + E) ∣      B  ⟶ (1 + E) ∣      B
  true     : ∀ {E B} →      E  ∣      B  ⟶      E  ∣ (1 + B)
  false    : ∀ {E B} →      E  ∣      B  ⟶      E  ∣ (1 + B)
  Bool-POP : ∀ {E B} →      E  ∣ (1 + B) ⟶      E  ∣      B
  AND      : ∀ {E B} →      E  ∣ (2 + B) ⟶      E  ∣ (1 + B)
  NOT      : ∀ {E B} →      E  ∣ (1 + B) ⟶      E  ∣ (1 + B)

data Deriv : ∀ {E B E' B'} → E ∣ B ⟶ E' ∣ B' → Set where
  []  : ∀ {E B} → Deriv (NOOP {E = E} {B = B})
  -- _∷_ : (x : a) (xs : Deriv ) → Deriv a

