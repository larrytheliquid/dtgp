open import Data.Nat
module Trans2 (W : Set) (In Out : W → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ : ℕ → ℕ → Set where
  []  : ∀ {n} → n ⟶ n

  _∷_ : ∀ {B n} →
    (w : W) → B ⟶ n + In w →
    B ⟶ (n ∸ In w) + Out w

_++_ : ∀ {Inw Outw B} →
  Inw ⟶ Outw →
  B ⟶ Inw →
  B ⟶ Outw
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
