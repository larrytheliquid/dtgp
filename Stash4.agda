open import Data.Nat
module Stash4 where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Function
import Data.List as L

infixr 5 _∷_ _++_

data Term (W : Set) (In Out : W → ℕ → ℕ) (A : ℕ) : ℕ → ℕ → Set where
  []  : Term W In Out A A zero

  _∷_ : ∀ {n k} →
    (w : W) → Term W In Out A (In w k) n →
    Term W In Out A (Out w k) (suc n)

_++_ : ∀ {W In Out A B C m n} →
  Term W In Out B C m →
  Term W In Out A B n →
  Term W In Out A C (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {W In Out A C m n} {In' Out' : Term W In Out A C m → ℕ → ℕ} → 
 Term (Term W In Out A C m) In' Out' A C n → Term W In Out A C (n * m)
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss
