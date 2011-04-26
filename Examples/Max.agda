module Examples.Max where
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.List hiding (sum)
open import Data.Vec hiding (init)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Stash

data Word : Set where
  nat : ℕ → Word
  plus times : Word

In : Word → ℕ → ℕ
In (nat _) n = n
In plus n = 2 + n
In times n = 2 + n

Out : Word → ℕ → ℕ
Out (nat _) n = 1 + n
Out plus n = 1 + n
Out times n = 1 + n

open Stash Word In Out

eval : ∀ {ins outs} → Term ins outs → Vec ℕ ins → Vec ℕ outs
eval [] as = as
eval (nat n ∷ xs) as with eval xs as
... | cs = n ∷ cs
eval (plus ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ + c₂) ∷ cs
eval (times ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs

score : Term _ _ → ℕ
score xs = sum (eval xs [])

open Evolution score

match : (w : Word) (out : ℕ) → ∃ λ k → Dec (out ≡ In w k)
match (nat _) n = n , yes refl
match plus zero = 0 , no λ ()
match plus (suc zero) = 0 , no λ ()
match plus (suc (suc n)) = n , yes refl
match times zero = 0 , no λ ()
match times (suc zero) = 0 , no λ ()
match times (suc (suc n)) = n , yes refl

open Initialization match

choices : List Word
choices = nat 1 ∷ nat 2 ∷ nat 3 ∷ plus ∷ times ∷ []

population : Population _ _ _
population = fromList (init 4 0 1 choices)

answer : Population _ _ _
answer = evolve 1337 1 population

