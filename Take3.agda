module Take3 where
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_∸_)

infixl 2 _⟶_
infixr 5 _,_
infixl 6 _∸_

_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

data Bool (B : ℕ) : ℕ → ℕ → Set where
  true  : Bool B 0 1
  not   : Bool B 1 1
  and   : Bool B 2 1
  dup   : Bool B 1 2
  flush : Bool B B 0

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _,_ :  ∀ {B B' In Out} →
    (w : Bool B' In Out) →
    B ⟶ B' →
    B + (In ∸ B') ⟶ (B' ∸ In) + Out

data Exec {B B' : ℕ} (E : B ⟶ B') :
  {C C' : ℕ} → C ⟶ C' →
  {D D' : ℕ} → D ⟶ D' →
  Set where

  const : ∀ {m₁ n₁ m₂ n₂} 
          {w₁ : Bool 0 m₁ n₁}
          {w₂ : Bool n₁ m₂ n₂}
          {w₃ : Bool 0 m₂ n₂}→
    Exec E (w₂ , w₁ , []) (w₃ , [])

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
