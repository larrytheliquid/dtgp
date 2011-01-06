open import Data.Nat
module This (W : Set) (In Out : W → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

infixl 2 _⟶_
infixr 5 _∷_ _++_ _t++_

data _⟶_ : ℕ → ℕ → Set where
  []  : ∀ {n} → n ⟶ n

  _∷_ : ∀ {B B'} →
    (w : W) → B ⟶ B' →
    B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)

_++_ : ∀ {C C' B B'} →
  C ⟶ C' →
  B ⟶ B' →
  ∃₂ _⟶_
[] ++ ys = _ , _ , ys
(x ∷ xs) ++ ys with xs ++ ys
... | _ , _ , ih = _ , _ , x ∷ ih

_t++_ : ∀ {Inw Outw B} →
  Inw ⟶ Outw →
  B ⟶ Inw →
  B ⟶ Outw
_t++_ {Outw = Outw} {B = B} [] ys = ?
_t++_ .{Outw = Out x + (B0 ∸ In x)} {B = B} (x ∷ xs) ys with (x ∷ xs) ++ ys
... | a , a' , ret = ?
-- with x ≟ B
-- ... | yes p rewrite p = {!!}
-- ... | no p = {!!}

-- [] t++ ys = ys
-- (x ∷ xs) t++ ys with xs ++ ys
-- ... | _ , _ , ih with x ∷ ih
-- ... | ret = {!!}
-- -- x ∷ (xs t++ ys)
