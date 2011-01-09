module Econ3 where
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

import Data.List as L

Out-List : L.List (ℕ × ℕ) → ℕ
Out-List L.[] = 0
Out-List (L._∷_ (B , B') xs) =
  Out B' B (Out-List xs)

In-List : L.List (ℕ × ℕ) → ℕ
In-List L.[] = 0
In-List (L._∷_ (B , B') xs) =
  In B (In-List xs) (Out-List xs)

data Econ : ℕ → ℕ → Set where
  []  : Econ 0 0
  cons : ∀ {old-in old-out} →
    (new-in new-out : ℕ) →
    Econ old-in old-out →
    Econ (In new-in old-in old-out) 
         (Out new-out new-in old-out)

from-List : (xs : L.List (ℕ × ℕ)) → Econ (In-List xs) (Out-List xs)
from-List L.[] = []
from-List (L._∷_ (B , B') xs) = cons B B' (from-List xs)
