open import Relation.Binary
module Poly (Domain : Set) (W : Set)
  (In Out : W → Domain → Domain)
where
open import Level
open import Function
open import Relation.Nullary
open import Data.Bool hiding (_≟_)
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.List hiding (length) renaming (_++_ to _l++_)
open import Data.Vec hiding (_++_; _>>=_; concat; map; init)
open import Stash.Rand

infixr 5 _∷_ -- _++_ _++'_

data Term (ins : Domain) : Domain → Set where
  []  : Term ins ins

  _∷_ : ∀ {k} (w : W) →
    Term ins (In w k) →
    Term ins (Out w k)
