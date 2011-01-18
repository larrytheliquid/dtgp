module Angeline97 where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Vec
import Stashy

data Word : Set where
  not and or : Word

In : Word → ℕ → ℕ
In not n = 1 + n
In and n = 2 + n
In or  n = 2 + n

Out : Word → ℕ → ℕ
Out not n = 1 + n
Out and n = 1 + n
Out or  n = 1 + n

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc zero)) = true
even (suc n) = even n

trues : ∀ {n} → Vec Bool n → ℕ
trues [] = 0
trues (true ∷ xs) = suc (trues xs)
trues (false ∷ xs) = trues xs

evenParity : ∀ {n} → Vec Bool n → Bool
evenParity xs = even (trues xs)

open Stashy Word In Out

population = 4
inputs = 2
outputs = 1
cases = 4

fitnessCases : Vec (Vec Bool inputs) cases
fitnessCases =
    (true ∷ true ∷ [])
  ∷ (true ∷ false ∷ [])
  ∷ (false ∷ true ∷ [])
  ∷ (false ∷ false ∷ [])
  ∷ []

score : Vec Bool inputs → Vec Bool outputs → ℕ
score xs (y ∷ []) = if evenParity xs ∧ y
  then 1 else 0

eval : ∀ {A C} → Term A C → Vec Bool A → Vec Bool C
eval [] as = as
eval (not ∷ xs) as with eval xs as
... | c ∷ cs = Data.Bool.not c ∷ cs
eval (and ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∧ c₂) ∷ cs
eval (or ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∨ c₂) ∷ cs

open Evolve Bool population inputs outputs cases fitnessCases score eval

random : Vec (Rand population) population
random =
    ((suc zero , suc (suc zero) , zero , suc (suc (suc zero))) , (6 , 7))
  ∷ ((suc (suc (suc zero)) , suc (suc zero) , zero , suc zero) , (9 , 5))
  ∷ ((suc zero , zero , suc (suc zero) , suc (suc (suc zero))) , (1 , 10))
  ∷ ((zero , suc (suc zero) , suc zero , suc (suc (suc zero))) , (3 , 8))
  ∷ []

initialPopulation : Population inputs outputs population
initialPopulation =
    (not ∷ and ∷ not ∷ [])
  ∷ (not ∷ and ∷ [])
  ∷ (not ∷ or ∷ [])
  ∷ (not ∷ or ∷ not ∷ [])
  ∷ []

evolved : Population inputs outputs population
evolved = evolve random initialPopulation
