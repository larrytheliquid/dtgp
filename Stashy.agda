open import Data.Nat
module Stashy (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Product hiding (map)
open import Data.Function
import Data.Vec as V

infixr 5 _∷_ _++_ _++'_

data Term (A : ℕ) : ℕ → Set where
  []  : Term A A

  _∷_ : ∀ {k} →
    (w : W) → Term A (In w k)→
    Term A (Out w k)

_++_ : ∀ {A B C} →
  Term B C →
  Term A B →
  Term A C
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {A C : ℕ} : Term A C → Set where
  _++'_ : ∀ {B}
    (xs : Term B C)
    (ys : Term A B) →
    Split (xs ++ ys)

split : ∀ {A C} (n : ℕ) (xs : Term A C) → Split xs
split zero xs = [] ++' xs
split (suc n) [] = [] ++' []
split (suc n) (x ∷ xs) with split n xs
split (suc A) (x ∷ ._) | xs ++' ys = (x ∷ xs) ++' ys

length : ∀ {A C} → Term A C → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

split-male : ∀ {A C} → ℕ → Term A C → ∃ (Term A)
split-male rand xs with rand mod (suc (length xs))
... | i with split (toℕ i) xs
split-male rand ._ | i | xs ++' ys = _ , ys

tails : ∀ {A D} B → Term A D → ∃ (V.Vec (Term A B))
tails B [] = _ , V.[]
tails B (_∷_ {k = k} x xs) with x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , V._∷_ x∷xs (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

split-female : ∀ {A C} {xs : Term A C} (rand : ℕ) →
  Split xs → Term A C
split-female {A = A} rand (_++'_ {B = B} xs ys)
  with tails B ys
split-female rand (xs ++' ys) | zero , V.[] = xs ++ ys
split-female rand (xs ++' ys) | suc n , zs
  = xs ++ (V.lookup (rand mod suc n) zs)
