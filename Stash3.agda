open import Data.Nat
module Stash3 (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Function
open import Data.Vec renaming (_++_ to _v++_)

infixr 5 _∷_ _++_

data Term (A : ℕ) : ℕ → {n : ℕ} → Vec ℕ n → Set where
  []  : Term A A []

  _∷_ : ∀ {n k} {xs : Vec ℕ n} →
    (w : W) → Term A (In w k) xs →
    Term A (Out w k) (Out w k ∷ xs)

_++_ : ∀ {A B C m n} {xs : Vec ℕ m} {ys : Vec ℕ n} →
  Term B C xs →
  Term A B ys →
  Term A C (xs v++ ys)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {m n A C : ℕ} {bs : Vec ℕ n} (as : Vec ℕ m) : Term A C (as v++ bs) → Set where
  _++'_ : ∀ {B}
    (xs : Term B C as)
    (ys : Term A B bs) →
    Split as (xs ++ ys)

split : ∀ {m n A C} {bs : Vec ℕ n} (as : Vec ℕ m)
  (xs : Term A C (as v++ bs)) → Split as xs
split [] xs = [] ++' xs
split (._ ∷ as) (x ∷ xs) with split as xs
split (._ ∷  as) (x ∷ ._) | xs ++' ys = (x ∷ xs) ++' ys
