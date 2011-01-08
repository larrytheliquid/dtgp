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
  _∷_ : ∀ {n} → (m : ℕ × ℕ) → Econ n → Econ (econ m n)

import Data.List as L

econ-List : L.List (ℕ × ℕ) → ℕ × ℕ
econ-List L.[] = 0 , 0
econ-List (L._∷_ x xs) = econ x (econ-List xs)

from-List : (xs : L.List (ℕ × ℕ)) → Econ (econ-List xs)
from-List L.[] = []
from-List (L._∷_ x xs) = x ∷ from-List xs

econs : ∀ {m n} → Econ m → Econ n → ℕ × ℕ
econs {n = n} [] ys = n
econs (x ∷ xs) ys = econ x (econs xs ys)

append : ∀ {m n} → (xs : Econ m) → (ys : Econ n) → Econ (econs xs ys)
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

private
  eg1 : Econ (1 , 3)
  eg1 = (1 , 1) ∷ (0 , 1) ∷ (0 , 1) ∷ (1 , 1) ∷ []

  eg2 : Econ (3 , 1)
  eg2 = (2 , 1) ∷ (2 , 1) ∷ []

  eg3 : Econ (1 , 3)
  eg3 = (1 , 2) ∷ (1 , 2) ∷ []



