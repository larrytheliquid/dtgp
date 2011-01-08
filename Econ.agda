module Econ where
open import Data.Nat
open import Data.Product

infixr 5 _∷_

econ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
econ (zero , zero) xy = xy
econ (m , suc n) xy with econ (m , n) xy
... | (x , y) = x , suc y
econ (suc m , n) xy with econ (m , n) xy
... | (x , zero) = suc x , zero
... | (x , suc y) = x , y

data Econ : ℕ × ℕ → Set where
  []  : Econ (0 , 0)
  _∷_ : ∀ {a} → (b : ℕ × ℕ) → Econ a → Econ (econ b a)

eg1 : Econ (1 , 3)
eg1 = (1 , 1) ∷ (0 , 1) ∷ (0 , 1) ∷ (1 , 1) ∷ []

eg2 : Econ (3 , 1)
eg2 = (2 , 1) ∷ (2 , 1) ∷ []


