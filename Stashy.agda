open import Data.Nat
module Stashy (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Product hiding (map)
open import Data.Function
open import Data.Vec hiding (_++_)

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

tails : ∀ {A D} B → Term A D → ∃ (Vec (Term A B))
tails B [] = _ , []
tails {A} .{Out x k} B (_∷_ {k = k} x xs)
  with Term A (Out x k) ∶ x ∷ xs | Out x k ≟ B
... | x∷xs | yes p rewrite p =
  _ , x∷xs ∷ (proj₂ (tails B xs))
... | x∷xs | no p = tails B xs

_++split♂_ : ∀ {A C} {xs : Term A C} →
  Split xs → (rand : ℕ) → Term A C
(_++'_ {B = B} xs ys) ++split♂ rand 
  with tails B ys
(xs ++' ys) ++split♂ rand | zero , [] = xs ++ ys
(xs ++' ys) ++split♂ rand | suc n , zs
  = xs ++ (lookup (rand mod suc n) zs)

crossover : ∀ {A C} (♀ ♂ : Term A C) (rand♀ rand♂ : ℕ) → Term A C
crossover ♀ male rand♀ rand♂ =
  split♀ ♀ rand♀ ++split♂ rand♂

Population : (A C n : ℕ) → Set
Population A C n = Vec (Term A C) n

open import Data.Bool
module Evolve (U : Set) (input : {n : ℕ} → Vec U n)
  (eval : {m n : ℕ} → Term m n → Vec U m → Vec U n)
  (better? : {n : ℕ} → Vec U n → Vec U n → Bool)
  where

  tournament : ∀ {A C n} (i j : Fin n) →
    Population A C n → Term A C
  tournament i j xss
    with lookup i xss
    |    lookup j xss
  ... | a | b = if
    better? (eval a input) (eval b input)
    then a else b

  evolve1 : ∀ {A C n} →
    (i j k l : Fin n) →
    (rand♀ rand♂ : ℕ) →
    Population A C n →
    Term A C
  evolve1 i j k l rand♀ rand♂ xss
    with tournament i j xss | tournament k l xss
  ... | ♀ | ♂ = crossover ♀ ♂ rand♀ rand♂

  Rand : ℕ → Set
  Rand n = (Fin n × Fin n × Fin n × Fin n) × (ℕ × ℕ)

  evolveN : ∀ {A C m n} →
    Vec (Rand m) n →
    Population A C m →
    Population A C n
  evolveN [] xss = []
  evolveN (((i , j , k , l) , (rand♀ , rand♂)) ∷ is) xss =
    evolve1 i j k l rand♀ rand♂ xss ∷ evolveN is xss

  evolve : ∀ {A C n} →
    Vec (Rand n) n →
    Population A C n →
    Population A C n
  evolve rands xss = evolveN rands xss