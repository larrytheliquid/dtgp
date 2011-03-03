module Examples.Max where
open import Data.Bool
open import Data.Nat
open import Data.Vec
import Stash

data Word : Set where
  two plus times : Word

In : Word → ℕ → ℕ
In two n = n
In plus n = 2 + n
In times n = 2 + n

Out : Word → ℕ → ℕ
Out two n = 1 + n
Out plus n = 1 + n
Out times n = 1 + n

open Stash Word In Out

eval : ∀ {ins outs} → Term ins outs → Vec ℕ ins → Vec ℕ outs
eval [] as = as
eval (two ∷ xs) as with eval xs as
... | cs = 2 ∷ cs
eval (plus ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ + c₂) ∷ cs
eval (times ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs

score : Term _ _ → ℕ
score xs = sum (eval xs [])

population : Population _ _ _
population =
    (plus ∷ plus ∷ two ∷ two ∷ two ∷ [])
  ∷ (times ∷ two ∷ two ∷ [])
  ∷ (plus ∷ times ∷ two ∷ plus ∷ two ∷ two ∷ two ∷ [])
  ∷ (times ∷ two ∷ plus ∷ two ∷ two ∷ [])
  ∷ []

open Evolution score

answer : Population _ _ _
answer = evolve 1337 1 population
