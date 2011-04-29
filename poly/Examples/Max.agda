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

pre : Word → ℕ → ℕ
pre (nat _) n = n
pre sucSuc n = 1 + n
pre times n = 2 + n

post : Word → ℕ → ℕ
post (nat _) n = 1 + n
post sucSuc n = 1 + n
post times n = 1 + n

open DTGP pre post Data.Nat._≟_

eval : ∀ {inp out} → Term inp out → Vec ℕ inp → Vec ℕ out
eval [] is = is
eval (nat o ∷ xs) is with eval xs is
... | os = o ∷ os
eval (sucSuc ∷ xs) is with eval xs is
... | o ∷ os = (2 + o) ∷ os
eval (times ∷ xs) is with eval xs is
... | o₂ ∷ o₁ ∷ os = (o₁ * o₂) ∷ os

score : Term 0 1 → ℕ
score xs = sum (eval xs [])

open Evolution score

match : (w : Word) (out : ℕ) → Dec (∃ λ n → out ≡ pre w n)
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

