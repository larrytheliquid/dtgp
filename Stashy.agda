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

split-female : ∀ {A C} → (xs : Term A C) → ℕ → Split xs
split-female xs rand with rand mod (suc (length xs))
... | i = split (toℕ i) xs

tails : ∀ {A D} B → Term A D → ∃ (V.Vec (Term A B))
tails B [] = _ , V.[]
tails B (_∷_ {k = k} x xs) with x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , V._∷_ x∷xs (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

_++split-male_ : ∀ {A C} {xs : Term A C} →
  Split xs → (rand : ℕ) → Term A C
(_++'_ {B = B} xs ys) ++split-male rand 
  with tails B ys
(xs ++' ys) ++split-male rand | zero , V.[] = xs ++ ys
(xs ++' ys) ++split-male rand | suc n , zs
  = xs ++ (V.lookup (rand mod suc n) zs)

crossover : ∀ {A C} (female male : Term A C) (rand-f rand-m : ℕ) → Term A C
crossover female male rand-f rand-m =
  split-female female rand-f ++split-male rand-m
