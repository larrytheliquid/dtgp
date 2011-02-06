open import Data.Nat
module Macro (D : Set) (W : Set) (Var : W → Set)
  (In Out : (w : W) → Var w → D)
  where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)

infixr 5 _∷_

data Term (A : D) : D → Set where
  []  : Term A A

  _∷_ : (w : W) {v : Var w} →
    Term A (In w v) →
    Term A (Out w v)

_++_ : ∀ {A B C} →
  Term B C →
  Term A B →
  Term A C
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)