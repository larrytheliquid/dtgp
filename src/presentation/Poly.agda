open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
module Poly
  {Domain Word : Set}
  (pre post : Word → Domain → Domain)
  (_≟_ : (x y : Domain) → Dec (x ≡ y))
where

infixr 5 _∷_ _++_ _++'_

data Term (inp : Domain) : Domain → Set where
  []  : Term inp inp

  _∷_ : ∀ {d} (w : Word) →
    Term inp (pre w d) → Term inp (post w d)

_++_ : ∀ {inp mid out} →
  Term mid out →
  Term inp mid →
  Term inp out
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {inp out} mid : Term inp out → Set where
  _++'_ :
    (xs : Term mid out)
    (ys : Term inp mid) →
    Split mid (xs ++ ys)
