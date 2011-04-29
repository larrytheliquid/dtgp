module Examples.Max where
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.List hiding (sum)
open import Data.Vec hiding (init)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import DTGP

data Word : Set where
  nat : ℕ → Word
  sucSuc times : Word

In : Word → ℕ → ℕ
In (nat _) n = n
In sucSuc n = 1 + n
In times n = 2 + n

Out : Word → ℕ → ℕ
Out (nat _) n = 1 + n
Out sucSuc n = 1 + n
Out times n = 1 + n

open DTGP Word In Out

eval : ∀ {ins outs} → Term ins outs → Vec ℕ ins → Vec ℕ outs
eval [] as = as
eval (nat n ∷ xs) as with eval xs as
... | cs = n ∷ cs
eval (sucSuc ∷ xs) as with eval xs as
... | c₁ ∷ cs = (2 + c₁) ∷ cs
eval (times ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs

score : Term 0 1 → ℕ
score xs = sum (eval xs [])

open Evolution score

match : (w : Word) (out : ℕ) → Dec (∃ λ n → out ≡ In w n)
match (nat _) n = yes (n , refl)
match sucSuc zero = no ¬p where
  ¬p : Σ ℕ (λ n → 0 ≡ suc n) → ⊥
  ¬p (_ , ())
match sucSuc (suc n) = yes (n , refl)
match times zero = no ¬p where
  ¬p : Σ ℕ (λ n → 0 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match times (suc zero) = no ¬p where
  ¬p : Σ ℕ (λ n → 1 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match times (suc (suc n)) = yes (n , refl)

open Initialization match

choices : List Word
choices = nat 1 ∷ nat 2 ∷ nat 3 ∷ sucSuc ∷ times ∷ []

population : Population _ _ _
population = fromList (init 4 0 1 choices)

answer : Population _ _ _
answer = evolve 1337 1 population

