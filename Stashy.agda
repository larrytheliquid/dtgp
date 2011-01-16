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

split♀ : ∀ {A C} → (xs : Term A C) → ℕ → Split xs
split♀ xs rand with rand mod (suc (length xs))
... | i = split (toℕ i) xs

tails : ∀ {A D} B → Term A D → ∃ (V.Vec (Term A B))
tails B [] = _ , V.[]
tails B (_∷_ {k = k} x xs) with x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , V._∷_ x∷xs (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

_++split♂_ : ∀ {A C} {xs : Term A C} →
  Split xs → (rand : ℕ) → Term A C
(_++'_ {B = B} xs ys) ++split♂ rand 
  with tails B ys
(xs ++' ys) ++split♂ rand | zero , V.[] = xs ++ ys
(xs ++' ys) ++split♂ rand | suc n , zs
  = xs ++ (V.lookup (rand mod suc n) zs)

crossover : ∀ {A C} (♀ ♂ : Term A C) (rand♀ rand♂ : ℕ) → Term A C
crossover ♀ male rand♀ rand♂ =
  split♀ ♀ rand♀ ++split♂ rand♂

Population : (A C n : ℕ) → Set
Population A C n = V.Vec (Term A C) n

Rands : ℕ → Set
Rands n = V.Vec ℕ n

evolve1 : ∀ {A C n} (♀ ♂ : Term A C) → (rand♀ rand♂ : ℕ) → Fin n →
  Population A C n → Population A C n
evolve1 ♀ ♂ rand♀ rand♂ i xss
  with crossover ♀ ♂ rand♀ rand♂ 
... | child = V._[_]≔_ xss i child

-- evolve : ∀ {A C m n} →
--   Rands 4 → V.Vec (Fin n) m →
--   Population A C n → Population A C n
-- evolve rands V.[] xss = xss
-- evolve rands (V._∷_ iY (V._∷_ iZ is)) xss = evolve2 iY iZ rands xss
-- evolve rands (V._∷_ i is) xss = xss
