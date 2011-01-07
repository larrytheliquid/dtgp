open import Data.Nat
module Stash (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function
import Data.List

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ (B : ℕ) : ℕ → Set where
  []  : B ⟶ B

  _∷_ : ∀ {k} →
    (w : W) → B ⟶ In w k →
    B ⟶ Out w k

_++_ : ∀ {Inw Outw B} →
  Inw ⟶ Outw →
  B ⟶ Inw →
  B ⟶ Outw
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

private
  add0 : ∀ n → n + 0 ≡ n
  add0 zero = refl
  add0 (suc n) with add0 n
  ... | p rewrite p = refl

init : ∀ w k → In w k ⟶ Out w k
init w k with _∷_ {k = k} w []
... | t rewrite
    add0 (In w k)
  | add0 (Out w k)
  = t

[_] : ∀ w → In w 0 ⟶ Out w 0
[_] w = init w 0

open Data.List

List-IO : (ws : List W) → ℕ × ℕ
List-IO [] = 0 , 0
List-IO (w ∷ ws) with List-IO ws
... | B , B'  = B + (In w B' ∸ B') , Out w B' + (B' ∸ In w B')

-- List-IO : (ws : List W) → ℕ × ℕ
-- List-IO = foldr
--   (λ w k →
--     In w (proj₁ k) ∸ proj₂ k ,
--     Out w (proj₂ k) ∸ proj₂ k)
--   (0 , 0)

-- from-list : (ws : List W) → List-In ws ⟶ List-Out ws
-- from-list B [] = {!!}
-- from-list B (x ∷ xs) = ?
