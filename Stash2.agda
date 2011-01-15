open import Data.Nat
module Stash2 (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Function
import Data.List as L

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
split (suc A) (x ∷ ._) | xs ++' ys = (x ∷ xs) ++' ys

data Prog (A : ℕ) : ℕ → ℕ → Set where
  []  : Prog A A zero

  _∷_ : ∀ {B C m n} →
    Term B C m → Prog A B n →
    Prog A C (m + n)

concat : ∀ {A C n} → Prog A C n → Term A C n
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

data Trisect (m : ℕ) {n o A D : ℕ} : Term A D (m + n + o) → Set where
  _++'_++'_ : ∀ {B C}
    (xs : Term C D m)
    (ys : Term B C n)
    (zs : Term A B o) →
    Trisect m ((xs ++ ys) ++ zs)

trisect : ∀ m n {o A D} (xs : Term A D (m + n + o)) → Trisect m xs
trisect zero zero xs = [] ++' [] ++' xs
trisect zero (suc n) xs = {!!}
trisect (suc m) zero xs = {!!}
trisect (suc m) (suc n) xs = {!!}

data Group {A C} (n : ℕ) : Term A C n → Set where
  concat' : (xss : Prog A C n) → Group n (concat xss)

group : ∀ {A C} n (xss : Prog A C n) → Group n (concat xss)
group zero xss = concat' xss
group (suc n) xss = {!!}
