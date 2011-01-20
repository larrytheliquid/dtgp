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

og : Term 2 1
og = and ∷ []

go : Term 3 2
go = and ∷ []

oggo : Term 3 1
oggo = og ++ go

more : Term 6 5
more = and ∷ []

hm : Term 3 1
hm = (and ∷ []) ++ (and ∷ [])
