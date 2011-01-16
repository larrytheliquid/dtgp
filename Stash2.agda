open import Data.Nat
module Stash2 (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Product hiding (map)
open import Data.Function
-- open import Data.Vec hiding (_++_; concat)

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

import Data.Vec as V
tails : ∀ {A D m} B → Term A D m  → ∃ (V.Vec (∃ (Term A B)))
tails B [] = _ , V.[]
tails B (_∷_ {k = k} x xs) with x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , V._∷_ (_ , x∷xs) (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

crossover : ∀ {A C m n} {xs : Term A C (m + n)} (rand : ℕ) →
  Split m xs → ∃ (Term A C)
crossover {A = A} rand (_++'_ {B = B} xs ys)
  with tails B ys
crossover rand (xs ++' ys) | zero , V.[] = _ , xs ++ ys
crossover rand (xs ++' ys) | suc n , zs
  with V.lookup (rand mod suc n) zs
... | _ , ys' = _ , xs ++ ys'

-- crossover rand (xs ++' []) = _ , xs
-- crossover rand (xs ++' (_∷_ {n = n} y ys)) =
--   V.lookup (rand mod suc n) (y ∷ ys)

-- inits on Prog?

-- import Data.List as L
-- all-n : ℕ → L.List ℕ
-- all-n zero = L.[]
-- all-n (suc n) = L._∷_ zero (L.map suc (all-n n))

-- import Data.List.All as A
-- splits : ∀ {n A C} (xs : Term A C n) → A.All (Σ ℕ λ m → Split m xs)
-- splits xs = ?
