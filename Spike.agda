module Spike where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Product
open import Data.Maybe

infixl 2 _⟶_
infixr 5 _,_

data Word (B : ℕ) : ℕ → ℕ → Set where
  true  : Word B 0 1
  not   : Word B 1 1
  and   : Word B 2 1
  dup   : Word B 1 2
  flush : Word B B 0

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _,_ : ∀ {B B' In Out} →
    (w : Word B' In Out) →
    B ⟶ B' →
    B + (In ∸ B') ⟶ (B' ∸ In) + Out

Term : Set
Term = ∃₂ _⟶_

Choices : ℕ → ℕ → Set
Choices B B' = ∃ (Vec (B ⟶ B'))

choices : Term → (B B' : ℕ) → Choices B B'
choices (.0 , .0 , []) B B' = _ , []
choices (.(B + (In ∸ B')) , .(B' ∸ In + Out) , _,_ {B} {B'} {In} {Out} w ws) C C'
  with choices (_ , _ , ws) C C' | C ≟ (B + (In ∸ B')) | C' ≟ (B' ∸ In + Out)
... | _ , ih | yes p | yes p' rewrite p | p' = _ , ((w , ws) ∷ ih)
... | ih | _ | _ = ih

choice : (seed B B' : ℕ) → Term → Maybe (B ⟶ B')
choice seed B B' t with choices t B B'
choice seed 0 0 _ | zero , [] = just []
choice seed _ _ _ | zero , [] = nothing
... | suc n , c ∷ cs = just (lookup (seed mod suc n) (c ∷ cs))

private
  not,[] : 1 ⟶ 1
  not,[] = not , []

  and,[] : 2 ⟶ 1
  and,[] = and , []

  true,[] : 0 ⟶ 1
  true,[] = true , []

  not,not,[] : 1 ⟶ 1
  not,not,[] = not , not , []

  and,not,[] : 2 ⟶ 1
  and,not,[] = and , not,[]

  true,and,[] : 2 ⟶ 2
  true,and,[] = true , and,[]

  and,and,[] : 3 ⟶ 1
  and,and,[] = and , and,[]

  true,true,[] : 0 ⟶ 2
  true,true,[] = true , true,[]

  true,true,not,[] : 1 ⟶ 3
  true,true,not,[] = true , true , not , []

  not,true,true,not,[] : 1 ⟶ 3
  not,true,true,not,[] = not , true,true,not,[]

  true,and,flush,[] : 2 ⟶ 2
  true,and,flush,[] = true , and , flush , []

  flush,true,and,[] : 2 ⟶ 0
  flush,true,and,[] = flush , true,and,[]
