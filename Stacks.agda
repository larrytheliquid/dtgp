module Stacks where
open import Data.Unit hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

Stacks : ℕ → Set
Stacks zero = ⊤
Stacks (suc n) = ℕ × Stacks n

postulate _⊢_≟_ : (n : ℕ) → Decidable {Stacks n} _≡_
