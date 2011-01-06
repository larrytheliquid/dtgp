open import Data.Nat
module That (W : Set) (In Out : W → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

infixl 2 _⟶_

data _⟶_ : ℕ → ℕ → Set where
  []  : ∀ {n} → n ⟶ n

  less : ∀ {B k} →
    (w : W) → B ⟶ suc (In w + k) →
    B ⟶ suc (Out w + k)

  equal : ∀ {B} →
    (w : W) → B ⟶ In w →
    B ⟶ Out w

_++_ : ∀ {Inw Outw B} →
  Inw ⟶ Outw →
  B ⟶ Inw →
  B ⟶ Outw
[] ++ ys = ys
(less x xs) ++ ys = less x (xs ++ ys)
(equal x xs) ++ ys = equal x (xs ++ ys)
