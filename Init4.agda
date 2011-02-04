open import Data.Nat
module Init4 (W : Set) (In : W → ℕ) (Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise; compare)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)
open import Data.List hiding (_++_)

infixr 5 _∷_ _++_

data Term (A : ℕ) : ℕ → Set where
  []  : Term A A

  _∷_ : ∀ {n} →
    (w : W) → Term A (In w + n) →
    Term A (Out w n)

_++_ : ∀ {A B C} →
  Term B C →
  Term A B →
  Term A C
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

ext : ∀ {A B} → (w : W) → Term A B → Maybe (∃ λ n → Term A (Out w n))
ext {B = B} x xs with compare B (In x)
ext x xs | equal ._ = {!!}
ext x xs | less _ ._ = {!!}
ext x xs | greater m k = {!!}

