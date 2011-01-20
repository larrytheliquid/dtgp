module Eg where
open import Data.Nat
import Stashy2

data Word : Set where
  true not and dup pop : Word

In : Word → ℕ → ℕ
In true n = n
In not n = 1 + n
In and n = 2 + n
In dup n = 1 + n
In pop n = 1 + n

Out : Word → ℕ → ℕ
Out true n = 1 + n
Out not n = 1 + n
Out and n = 1 + n
Out dup n = 2 + n
Out pop n = n

open Stashy2 Word In Out

bc : Term 2 1
bc = and ∷ []

ab : Term 3 2
ab = and ∷ []

abc : Term 3 1
abc = bc ++ ab

more : Term 6 5
more = and ∷ []

big : Term 10 8
big = (and ∷ []) ++ (and ∷ [])
