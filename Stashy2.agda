open import Data.Nat
module Stashy2 (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
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

data Split {A C : ℕ} (B : ℕ) : Term A C → Set where
  _++'_ :
    (xs : Term B C)
    (ys : Term A B) →
    Split B (xs ++ ys)

swap₁ : ∀ {A B C} {xs ys : Term A C} →
  Split B xs → Split B ys → Term A C
swap₁ (xs ++' ys) (as ++' bs) = xs ++ bs

swap₂ : ∀ {A B C} {xs ys : Term A C} →
  Split B xs → Split B ys → Term A C
swap₂ (xs ++' ys) (as ++' bs) = as ++ ys

split : ∀ {A C} (n : ℕ) (xs : Term A C) → ∃ λ B → Split B xs
split zero xs = _ , [] ++' xs
split (suc n) [] = _ , [] ++' []
split (suc n) (x ∷ xs) with split n xs
split (suc A) (x ∷ ._) | _ , xs ++' ys = _ , (x ∷ xs) ++' ys

splits : ∀ {A C} (n : ℕ) (B : ℕ) → (xs : Term A C) → ∃ (Vec (Split B xs))
splits zero B xs with split zero xs
... | B' , ys with B ≟ B'
... | yes p rewrite p = _ , ys ∷ []
... | no p = _ , []
splits (suc n) B xs with split (suc n) xs
... | B' , ys with B ≟ B' | splits n B xs
... | yes p | _ , yss rewrite p = _ , ys ∷ yss
... | no p | _ , yss = _ , yss

length : ∀ {A C} → Term A C → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

split♀ : ∀ {A C} → (xs : Term A C) → ℕ → ∃ λ B → Split B xs
split♀ xs rand with rand mod (suc (length xs))
... | i = split (toℕ i) xs

split♂ : ∀ {A C} (xs : Term A C) →
  (B rand : ℕ) → Maybe (Split B xs)
split♂ xs B rand
  with splits (length xs) B xs
... | zero , [] = nothing
... | suc n , xss
  = just (lookup (rand mod suc n) xss)

crossover : ∀ {A C} (♀ ♂ : Term A C) (rand♀ rand♂ : ℕ) → Term A C × Term A C
crossover ♀ ♂ rand♀ rand♂
  with split♀ ♀ rand♀
... | B , xs with  split♂ ♂ B rand♂
... | nothing = ♀ , ♂
... | just ys = swap₁ xs ys , swap₂ xs ys

Population : (A C n : ℕ) → Set
Population A C n = Vec (Term A C) n
