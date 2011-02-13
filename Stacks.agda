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

data MaybeDec (P : Set) : Set where
  just : (p : P) → MaybeDec P
  nothing : MaybeDec P

MaybeDecidable : {a : Set} → Rel a → Set
MaybeDecidable _∼_ = ∀ x y → MaybeDec (x ∼ y)

_⊢_≟_ : (n : ℕ) → MaybeDecidable {Stacks n} _≡_
zero ⊢ x ≟ y with x ≟u y
... | yes p = just p
... | no p = nothing
suc n ⊢ (x , xs) ≟ (y , ys)
  with x ≟n y | n ⊢ xs ≟ ys
suc n ⊢ (x , xs) ≟ (._ , ._) | yes refl | just refl = just refl
suc n ⊢ (x , xs) ≟ (y , ys) | no p | nothing  = nothing
suc n ⊢ (x , xs) ≟ (y , ._) | no p | just refl = nothing
suc n ⊢ (x , xs) ≟ (._ , ys) | yes refl | nothing = nothing
