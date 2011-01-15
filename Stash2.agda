open import Data.Nat
module Stash2 (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Function

infixr 5 _∷_ _++_

data Term (A : ℕ) : ℕ → ℕ → Set where
  []  : Term A A zero

  _∷_ : ∀ {n k} →
    (w : W) → Term A (In w k) n →
    Term A (Out w k) (suc n)

_++_ : ∀ {A B C m n} →
  Term B C m →
  Term A B n →
  Term A C (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split (m : ℕ) {n A C : ℕ} : Term A C (m + n) → Set where
  _++'_ : ∀ {B}
    (xs : Term B C m)
    (ys : Term A B n) →
    Split m (xs ++ ys)

split : ∀ m {n A C} (xs : Term A C (m + n)) → Split m xs
split zero xs = [] ++' xs
split (suc m) (x ∷ xs) with split m xs
split (suc A) (x ∷ .(xs ++ ys)) | xs ++' ys = (x ∷ xs) ++' ys

take : ∀ {A C} m {n} → Term A C (m + n) → Σ ℕ λ B → Term B C m
take m xs with split m xs
take m .(xs ++ ys) | xs ++' ys = _ , xs

drop : ∀ {A C} m {n} → Term A C (m + n) → Σ ℕ λ B → Term A B n
drop m xs with split m xs
drop m .(xs ++ ys) | xs ++' ys = _ , ys
