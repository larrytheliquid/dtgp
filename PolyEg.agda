module PolyEg where
open import Data.Nat renaming (_≟_ to _≟n_)
open import Relation.Binary.PropositionalEquality
import Poly

infixr 4 _,_

data Word : Set where
  not suc gt : Word

record Domain : Set where
  constructor _,_
  field
    bools : ℕ
    nats : ℕ

---------------------------------------------------------
open import Relation.Nullary
open import Relation.Binary

data MaybeDec (P : Set) : Set where
  just : (p : P) → MaybeDec P
  nothing : MaybeDec P

_≟_ : (x y : Domain) → MaybeDec (x ≡ y)
(bs , ns) ≟ (bs' , ns') with bs ≟n bs' | ns ≟n ns'
... | yes p | yes p' rewrite p | p' = just refl
... | _ | _ = nothing

---------------------------------------------------------

In : Word → Domain → Domain
In not (m , n) = m , 1 + n
In suc (m , n) = m , 1 + n
In gt (m , n) = m , n + 2

Out : Word → Domain → Domain
Out not (m , n) = 1 + m , n
Out suc (m , n) = m , 1 + n
Out gt (m , n) = 1 + m , n

open Poly Domain Word In Out

eg : Term (0 , 2) (1 , 0)
eg = gt ∷ []

Domain-≡ : record {bools = 5 ; nats = 3} ≡ (5 , 3)
Domain-≡ = refl 
