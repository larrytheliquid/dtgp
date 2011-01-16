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

splitFemale : ∀ {A C} → (xs : Term A C) → ℕ → Split xs
splitFemale xs rand with rand mod (suc (length xs))
... | i = split (toℕ i) xs

tails : ∀ {A D} B → Term A D → ∃ (V.Vec (Term A B))
tails B [] = _ , V.[]
tails B (_∷_ {k = k} x xs) with x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , V._∷_ x∷xs (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

_++splitMale_ : ∀ {A C} {xs : Term A C} →
  Split xs → (rand : ℕ) → Term A C
(_++'_ {B = B} xs ys) ++splitMale rand 
  with tails B ys
(xs ++' ys) ++splitMale rand | zero , V.[] = xs ++ ys
(xs ++' ys) ++splitMale rand | suc n , zs
  = xs ++ (V.lookup (rand mod suc n) zs)

crossover : ∀ {A C} (female male : Term A C) (randF randM : ℕ) → Term A C
crossover female male randF randM =
  splitFemale female randF ++splitMale randM

Population : (A C n : ℕ) → Set
Population A C n = V.Vec (Term A C) n

Rands : ℕ → Set
Rands n = V.Vec ℕ n

evolve2 : ∀ {A C n} (iY iZ : Fin n) → Rands 4 →
  Population A C n → Population A C n
evolve2 iY iZ rands xss
  with V.lookup iY xss | V.lookup iZ xss
... | ys | zs
  with crossover ys zs (V.lookup zero rands)
                       (V.lookup (suc zero) rands)
  |    crossover ys zs (V.lookup (suc (suc zero)) rands)
                       (V.lookup (suc (suc (suc zero))) rands)
... | ys' | zs'
  with V._[_]≔_ xss iY ys'
... | xss' =
  V._[_]≔_ xss' iZ zs'

evolve : ∀ {A C m n} →
  Rands 4 → V.Vec (Fin n) m →
  Population A C n → Population A C n
evolve rands V.[] xss = xss
evolve rands (V._∷_ iY (V._∷_ iZ is)) xss = evolve2 iY iZ rands xss
evolve rands (V._∷_ i is) xss = xss
