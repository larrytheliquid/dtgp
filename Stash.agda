open import Data.Nat
module Stash (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; pred)
open import Data.Vec hiding (replicate; map) renaming (_++_ to _v++_)
open import Data.Product hiding (map)
open import Data.Maybe

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _∷_ : ∀ {A A'} →
    (w : W) → A ⟶ A' →
    A + (In w A' ∸ A') ⟶ Out w A' + (A' ∸ In w A')

Term : Set
Term = ∃₂ _⟶_

_++_ : ∀ {A A' B B'} →
  B ⟶ B' → A ⟶ A' → Term
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

Candidates : ℕ → ℕ → Set
Candidates A A' = ∃ (Vec (A ⟶ A'))

to-Terms : ∀ {A A'} → Candidates A A' → Terms
to-Terms (zero , []) = _ , []
to-Terms (suc n , xs ∷ xss)
  = _ , (_ , _ , xs) ∷ (proj₂ (to-Terms (_ , xss)))

candidates : (A A' : ℕ) → Terms → Candidates A A'
candidates A A' (._ , []) = _ , []
candidates A A' (._ , (B , B' , xs) ∷ xss)
  with candidates A A' (_ , xss)
  |    A  ≟ B
  |    A' ≟ B'
... | _ , ih | yes p | yes p'
  rewrite p | p' = _ , xs ∷ ih
... | _ , ih | _ | _ = _ , ih

rand-term : ℕ → Terms → Term
rand-term seed (zero , []) = _ , _ , []
rand-term seed (suc n , xs ∷ xss) =
  lookup (seed mod suc n) (xs ∷ xss)

rand-candidate : ∀ {A A'} → ℕ → Candidates A A' → Maybe (A ⟶ A')
rand-candidate seed (._ , []) = nothing
rand-candidate seed (suc n , xs ∷ xss) =
  just (lookup (seed mod suc n) (xs ∷ xss))

map : (Term → Term) → Terms → Terms
map f (._ , []) = _ , []
map f (._ , (xs ∷ xss)) =
  _ , f xs ∷ proj₂ (map f (_ , xss))

inits : Term → Terms
inits (._ , ._ , []) = _ , (_ , _ , []) ∷ []
inits (._ , ._ , x ∷ xs) = _ , (_ , _ , []) ∷
  proj₂ (map (λ ys → _ , _ , x ∷ proj₂ (proj₂ ys))
             (inits (_ , _ , xs)))

tails : Term → Terms
tails (._ , ._ , []) = _ , (_ , _  , []) ∷ []
tails (._ , ._ , x ∷ xs ) =
  _ , (_ , _ , x ∷ xs) ∷ proj₂ (tails (_ , _ , xs))

split-male : ℕ → Term → Term
split-male seed xs =
  rand-term seed (inits xs)

split-female : (seed A A' : ℕ) → Term → Maybe (A ⟶ A')
split-female seed A A' xs =
  rand-candidate seed (candidates A A' (tails xs))

crossover : ℕ → ℕ → Term → Term → Term
crossover male-seed female-seed male female
  with split-male male-seed male
... | A , A' , male'
  with split-female female-seed A A' (_ , _ , male')
... | nothing = male
... | just female' = male' ++ female'

mutate : ℕ → ℕ → Term → Terms → Term
mutate male-seed mutation-seed male bank
  with split-male male-seed male
... | A , A' , male'
  with rand-candidate mutation-seed (candidates A A' bank)
... | nothing = male
... | just mutation = male' ++ mutation
