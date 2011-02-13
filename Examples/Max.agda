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

eval : ∀ {A C} → Term A C → Vec ℕ A → Vec ℕ C
eval [] as = as
eval (two ∷ xs) as with eval xs as
... | cs = 2 ∷ cs
eval (plus ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ + c₂) ∷ cs
eval (times ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs

score : ∀ {A C} → Term A C → ℕ
score xs = sum (eval xs (replicate 2))

population : Population 0 1 _
population =
    (plus ∷ plus ∷ two ∷ two ∷ two ∷ [])
  ∷ (times ∷ two ∷ two ∷ [])
  ∷ (plus ∷ times ∷ two ∷ plus ∷ two ∷ two ∷ two ∷ [])
  ∷ (times ∷ two ∷ plus ∷ two ∷ two ∷ [])
  ∷ []

answer : Population 0 1 _
answer = evolve score 1337 population
