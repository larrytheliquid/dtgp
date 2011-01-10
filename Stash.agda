open import Data.Nat
module Stash (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; pred)
open import Data.Vec hiding (replicate) renaming (_++_ to _v++_)
open import Data.Product hiding (map)
open import Data.Maybe

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _∷_ : ∀ {B B'} →
    (w : W) → B ⟶ B' →
    B + (In w B' ∸ B') ⟶ Out w B' + (B' ∸ In w B')

Term : Set
Term = ∃₂ _⟶_

_++_ : ∀ {A A' B B'} →
  A ⟶ A' → B ⟶ B' → Term
[] ++ ys = _ , _ , ys
(x ∷ xs) ++ ys with xs ++ ys
... | _ , _ , ih = _ , _ , (x ∷ ih)

Terms : Set
Terms = ∃ (Vec Term)

import Data.List as L

from-List : L.List W → Term
from-List L.[] = _ , _ , []
from-List (L._∷_ x xs) with from-List xs
... | _ , _ , ih = _ , _ , x ∷ ih

Choices : ℕ → ℕ → Set
Choices B B' = ∃ (Vec (B ⟶ B'))

choices : Term → (B B' : ℕ) → Choices B B'
choices (.0 , .0 , []) B B' = _ , []
choices (.(B + (In w B' ∸ B')) , .(Out w B' + (B' ∸ In w B')) , _∷_ {B} {B'} w ws) C C'
  with choices (_ , _ , ws) C C' | C ≟ (B + (In w B' ∸ B')) | C' ≟ (Out w B' + (B' ∸ In w B'))
... | _ , ih | yes p | yes p' rewrite p | p' = _ , ((w ∷ ws) ∷ ih)
... | ih | _ | _ = ih

choice : (seed B B' : ℕ) → Term → Maybe (B ⟶ B')
choice seed B B' t with choices t B B'
choice seed 0 0 _ | zero , [] = just []
choice seed _ _ _ | zero , [] = nothing
... | suc n , c ∷ cs = just (lookup (seed mod suc n) (c ∷ cs))

crossover : (seed B B' : ℕ) → 
  (male : Term) → (female : Term) → Term
crossover seed B B' male female
  with choice seed B B' female
... | nothing = male
... | just t = proj₂ (proj₂ male) ++ t

