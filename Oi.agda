open import Data.Nat
open import Data.List hiding (_++_)
module Oi (W : Set)
  (In-B Out-B : W → ℕ → ℕ)
  (In-T Out-T : W → List W → List W)
  where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function

infixr 5 _∷_

Term : Set
Term = List W

data Typing : Term → ℕ → Set where
  []  : ∀ {b} → Typing [] b

  _∷_ : ∀ {n t} →
    (w : W) → Typing (In-T w t) (In-B w n) →
    Typing (Out-T w t) (Out-B w n)

