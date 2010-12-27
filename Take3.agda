module Take3 where
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.Vec

_at-least_ : ℕ → ℕ → ℕ
at at-least least = (least ∸ at) + at

data Type : ℕ → ℕ → Set where
  empty : Type 0 0

  true  : ∀ {B B'} →
    Type B B' →
    Type B' (suc B')

  NOT :  ∀ {B B'} →
    Type B B' →
    Type (B at-least 1) (B' at-least 1)

  AND :  ∀ {B B'} →
    Type B B' →
    Type (B at-least 2) (B' at-least 1)

private
  not' : Type 1 1
  not' = NOT empty

  and : Type 2 1
  and = AND empty

  not,not : Type 1 1
  not,not = NOT not'

  and,not : Type 2 1
  and,not = AND not'

  -- and,and : Type 3 1
  -- and,and = AND and
