module Stacks where
open import Data.Unit renaming (_≟_ to _≟u_)
open import Data.Nat renaming (_≟_ to _≟n_)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

Stacks : ℕ → Set
Stacks zero = ⊤
Stacks (suc n) = ℕ × Stacks n

_⊢_≟_ : (n : ℕ) → Decidable {Stacks n} _≡_
zero ⊢ x ≟ y = x ≟u y
suc n ⊢ (x , xs) ≟ (y , ys)
  with x ≟n y | n ⊢ xs ≟ ys
suc n ⊢ (x , xs) ≟ (y , ys) | no p | no ih = {!!}
suc n ⊢ (x , xs) ≟ (y , ._) | no p | yes refl = {!!}
suc n ⊢ (x , xs) ≟ (._ , ys) | yes refl | no ih = {!!}
suc n ⊢ (x , xs) ≟ (._ , ._) | yes refl | yes refl = yes refl
