module Eg where
open import Data.Bool renaming (not to ¬)
open import Data.Nat
open import Data.Vec renaming (_++_ to _v++_)
import Stashy2

data Word : Set where
  true false not and or dup swap pop square : Word

In : Word → ℕ → ℕ
In true n = n
In false n = n
In not n = 1 + n
In and n = 2 + n
In or n = 2 + n
In dup n = 1 + n
In swap n = 2 + n
In pop n = 1 + n
In square n = n

Out : Word → ℕ → ℕ
Out true n = 1 + n
Out false n = 1 + n
Out not n = 1 + n
Out and n = 1 + n
Out or n = 1 + n
Out dup n = 2 + n
Out swap n = 2 + n
Out pop n = n
Out square n = n * n

open Stashy2 Word In Out

a : Term 3 3
a = []

b : Term 3 2
b = and ∷ a

c : Term 3 1
c = and ∷ b

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


eval : ∀ {A C} → Term A C → Vec Bool A → Vec Bool C
eval [] as = as
eval (true ∷ xs) as = true ∷ eval xs as
eval (false ∷ xs) as = false ∷ eval xs as
eval (not ∷ xs) as with eval xs as
... | c ∷ cs = ¬ c ∷ cs
eval (and ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∧ c₂) ∷ cs
eval (or ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∨ c₂) ∷ cs
eval (dup ∷ xs) as with eval xs as
... | c ∷ cs = c ∷ c ∷ cs
eval (swap ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = c₁ ∷ c₂ ∷ cs
eval (pop ∷ xs) as with eval xs as
... | c ∷ cs = cs
eval (_∷_ {k = n} square xs) as with eval xs as
... | cs = concat (replicate {n = n} cs)

