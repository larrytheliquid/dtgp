open import Data.Nat
module Stashy3 (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)

infixr 5 _∷_ -- _++_ _++'_

data Term (A : ℕ) : ℕ → ℕ → Set where
  []  : Term A A zero

  _∷_ : ∀ {k n} →
    (w : W) → Term A (In w k) n →
    Term A (Out w k) (suc n)

_++_ : ∀ {A B C m n} →
  Term B C m →
  Term A B n →
  Term A C (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {A C n : ℕ} (B m : ℕ) : Term A C (m + n) → Set where
  _++'_ :
    (xs : Term B C m)
    (ys : Term A B n) →
    Split B m (xs ++ ys)

swap₁ : ∀ {A B C m n m' n'} {xs : Term A C (m + n)} {ys : Term A C (m' + n')} →
  Split B m xs → Split B m' ys → Term A C (m + n')
swap₁ (xs ++' ys) (as ++' bs) = xs ++ bs

swap₂ : ∀ {A B C m n m' n'} {xs : Term A C (m + n)} {ys : Term A C (m' + n')} →
  Split B m xs → Split B m' ys → Term A C (m' + n)
swap₂ (xs ++' ys) (as ++' bs) = as ++ ys

split : ∀ {A C n} (m : ℕ) (xs : Term A C (m + n)) → ∃ λ B → Split B m xs
split zero xs = _ , [] ++' xs
split (suc n) (x ∷ xs) with split n xs
split (suc A) (x ∷ ._) | _ , xs ++' ys = _ , (x ∷ xs) ++' ys

-- splits : ∀ {A C n} (B : ℕ) → (xs : Term A C n) → ∃ (Vec (∃ λ m → Split B m xs))
-- splits {zero} B xs with split zero xs
-- ... | B' , ys with B ≟ B'
-- ... | yes p rewrite p = ? -- _ , ys ∷ []
-- ... | no p = ? -- _ , []
-- splits {suc n} B xs = ?
-- with split (suc n) xs
-- ... | B' , ys with B ≟ B' | splits n B xs
-- ... | yes p | _ , yss rewrite p = _ , ys ∷ yss
-- ... | no p | _ , yss = _ , yss

-- length : ∀ {A C} → Term A C → ℕ
-- length [] = 0
-- length (x ∷ xs) = suc (length xs)

-- split♀ : ∀ {A C} → (xs : Term A C) → ℕ → ∃ λ B → Split B xs
-- split♀ xs rand with rand mod (suc (length xs))
-- ... | i = split (toℕ i) xs

-- split♂ : ∀ {A C} (xs : Term A C) →
--   (B rand : ℕ) → Maybe (Split B xs)
-- split♂ xs B rand
--   with splits (length xs) B xs
-- ... | zero , [] = nothing
-- ... | suc n , xss
--   = just (lookup (rand mod suc n) xss)

-- crossover : ∀ {A C} (♀ ♂ : Term A C) (rand♀ rand♂ : ℕ) → Term A C × Term A C
-- crossover ♀ ♂ rand♀ rand♂
--   with split♀ ♀ rand♀
-- ... | B , xs with  split♂ ♂ B rand♂
-- ... | nothing = ♀ , ♂
-- ... | just ys = swap₁ xs ys , swap₂ xs ys

-- Population : (A C n : ℕ) → Set
-- Population A C n = Vec (Term A C) n
