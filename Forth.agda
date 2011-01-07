module Forth where
open import Data.Nat
import Stash

data Word : Set where
  nat : ℕ → Word
  nat-x nat-z
    plus minus
    times div
    : Word

In : Word → ℕ → ℕ
In (nat _) N = N
In nat-x   N = N
In nat-z   N = N
In _       N = 2 + N

Out : Word → ℕ → ℕ
Out _ N = 1 + N

open Stash Word In Out

term : 0 ⟶ 1
term = div ∷ plus ∷ div ∷ nat-x ∷ nat-z ∷ div ∷
  nat-z ∷ nat 2 ∷ minus ∷ times ∷ nat-z ∷ nat 4 ∷
  times ∷ nat-x ∷ nat 8 ∷ []

term1 : 0 ⟶ 3
term1 = nat-z ∷ nat 4 ∷
  times ∷ nat-x ∷ nat 8 ∷ []

term2 : 3 ⟶ 1
term2 = div ∷ plus ∷ div ∷ nat-x ∷ nat-z ∷ div ∷
  nat-z ∷ nat 2 ∷ minus ∷ times ∷ []

term' : 0 ⟶ 1
term' = term2 ++ term1

segment2 : 2 ⟶ 3
segment2 = nat-z ∷ div ∷ nat-z ∷ []

segment1 : 2 ⟶ 3
segment1 =  nat-z ∷ nat 4 ∷ times  ∷ []

original : 0 ⟶ 1
original = (div ∷ plus ∷ div ∷ nat-x ∷ nat-z ∷ div ∷
  nat-z ∷ nat 2 ∷ minus ∷ times ∷ [])
  ++ segment1 ++ (nat-x ∷ nat 8 ∷ [])

offspring : 0 ⟶ 1
offspring = (div ∷ plus ∷ div ∷ nat-x ∷ nat-z ∷ div ∷
  nat-z ∷ nat 2 ∷ minus ∷ times ∷ [])
  ++ segment2 ++ (nat-x ∷ nat 8 ∷ [])

