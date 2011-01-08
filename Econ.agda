module Econ where
open import Data.Nat
open import Data.Product

infixr 5 _∷_

esuc : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
esuc (zero , zero) xy = xy
esuc (m , suc n) xy with esuc (m , n) xy
... | (x , y) = x , suc y
esuc (suc m , n) xy with esuc (m , n) xy
... | (x , zero) = suc x , zero
... | (x , suc y) = x , y

data Econ : ℕ × ℕ → Set where
  []  : Econ (0 , 0)
  _∷_ : ∀ {n} → (m : ℕ × ℕ) → Econ n → Econ (esuc m n)

import Data.List as L

esuc-List : L.List (ℕ × ℕ) → ℕ × ℕ
esuc-List L.[] = 0 , 0
esuc-List (L._∷_ x xs) = esuc x (esuc-List xs)

from-List : (xs : L.List (ℕ × ℕ)) → Econ (esuc-List xs)
from-List L.[] = []
from-List (L._∷_ x xs) = x ∷ from-List xs

esuc-Econ : ∀ {m n} → Econ m → Econ n → ℕ × ℕ
esuc-Econ {n = n} [] ys = n
esuc-Econ (x ∷ xs) ys = esuc x (esuc-Econ xs ys)

append : ∀ {m n} → (xs : Econ m) → (ys : Econ n) → Econ (esuc-Econ xs ys)
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

private
  eg1 : Econ (1 , 3)
  eg1 = (1 , 1) ∷ (0 , 1) ∷ (0 , 1) ∷ (1 , 1) ∷ []

  eg2 : Econ (3 , 1)
  eg2 = (2 , 1) ∷ (2 , 1) ∷ []

  eg3 : Econ (1 , 3)
  eg3 = (1 , 2) ∷ (1 , 2) ∷ []



