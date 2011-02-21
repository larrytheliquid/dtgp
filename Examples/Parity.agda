module Examples.Parity where
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

eval : ∀ {ins outs} → Term ins outs → Vec Bool ins → Vec Bool outs
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

scores : ∀ {ins outs n} → Vec (Vec Bool ins) n → Term ins outs → ℕ
scores ass xs = sum (map (λ as →
  if (match (eval xs as) [ evenParity as ])
  then 1 else 0)
  ass)

fitnessCases : Vec (Vec Bool _) _
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

score : Term _ _ → ℕ
score xs = scores fitnessCases xs

population : Population _ _ _
population =
    (not ∷ and ∷ not ∷ [])
  ∷ (not ∷ and ∷ [])
  ∷ (not ∷ not ∷ not ∷ or ∷ [])
  ∷ (not ∷ or ∷ not ∷ [])
  ∷ []

open GP 2 1 score

answer : Population _ _ _
answer = evolve 1337 1 population

