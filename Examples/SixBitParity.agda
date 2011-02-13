module Examples.SixBitParity where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Vec
import Stash

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

open Stash Word In Out

eval : ∀ {A C} → Term A C → Vec Bool A → Vec Bool C
eval [] as = as
eval (not ∷ xs) as with eval xs as
... | c ∷ cs = Data.Bool.not c ∷ cs
eval (and ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∧ c₂) ∷ cs
eval (or ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∨ c₂) ∷ cs

match : ∀ {m n} → Vec Bool m → Vec Bool n → Bool
match [] [] = true
match (_ ∷ _) [] = false
match [] (_ ∷ _) = false
match (x ∷ xs) (y ∷ ys) = x ∧ y ∧ match xs ys

scores : ∀ {A C n} → Vec (Vec Bool A) n → Term A C → ℕ
scores ass xs = sum (map (λ as →
  if (match (eval xs as) [ evenParity as ])
  then 1 else 0)
  ass)

fitnessCases : Vec (Vec Bool 2) 4
fitnessCases =
    (true ∷ true ∷ [])
  ∷ (true ∷ false ∷ [])
  ∷ (false ∷ true ∷ [])
  ∷ (false ∷ false ∷ [])
  ∷ []

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc m == suc n = m == n

-- score : ∀ {A C} → Term A C → ℕ
-- score {A} {C} xs = (A == 2) ∧ scores fitnessCases xs

score : ∀ {A C} → Term A C → ℕ
score xs = trues (eval xs (replicate true))

population : Population 2 1 _
population =
    (not ∷ and ∷ not ∷ [])
  ∷ (not ∷ and ∷ [])
  ∷ (not ∷ not ∷ not ∷ or ∷ [])
  ∷ (not ∷ or ∷ not ∷ [])
  ∷ []

answer : Population 2 1 _
answer = evolve score 1337 population

