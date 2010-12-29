module Crossover where
open import Relation.Nullary
open import Data.Bool
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin
open import Data.List hiding (_++_)
open import Data.List.All hiding (lookup)
open import Data.Vec hiding (lookup)
open import Data.Product
open import Stash
open import Check

Terms : Set
Terms = List (Σ ℕ Term)

subterms : ∀ {n} → Term n → Terms
subterms [] = []
subterms (t ∷ ts) with subterms ts
... | xs = (_ , t ∷ ts) ∷ xs

Checks : Terms → ℕ → ℕ → Set
Checks ts B N = All (λ t → Typed (proj₂ t) B N) ts

checks : (ts : Terms) (B N : ℕ) → Checks ts B N
checks [] B N = []
checks (t ∷ ts) B N = check' (proj₂ t) B N ∷ checks ts B N

wells : ∀ {ts B N} → Checks ts B N → Terms
wells [] = []
wells (well d ∷ ps) = (_ , to-term d) ∷ wells ps
wells (ill ∷ ps) = wells ps

Choices : Terms → ℕ → ℕ → Set
Choices ts B N = All (λ t → (proj₂ t) ∶ B ∣ N) ts

choices : ∀ {ts B N} → (ps : Checks ts B N) →
  Choices (wells ps) B N
choices [] = []
choices (well d ∷ ps) = d ∷ choices ps
choices (ill ∷ ps) = choices ps

to-terms : ∀ {ts B N} →
  Choices ts B N → Σ Terms (λ ts → Choices ts B N)
to-terms ds = _ , ds

rand : (ts : Terms) → ℕ → Fin (suc (length ts))
rand ts n = n mod suc (length ts)

lookup : ∀ {ts B N} →
  Choices ts B N → Fin (suc (length ts)) → Σ ℕ Term
lookup [] i = 0 , []
lookup (d ∷ ds) zero = _ , to-term d
lookup (d ∷ ds) (suc i) = lookup ds i

subterm : ∀ {n} (seed B N : ℕ) → (t : Term n) → Σ ℕ Term
subterm seed B N t with choices (checks (subterms t) B N)
... | ds = lookup ds (rand (proj₁ (to-terms ds)) seed)

crossover : ∀ {m n} (seed B N : ℕ) → 
  (male : Term m) (female : Term n) → Σ ℕ Term
crossover seed B N male female =
  _ , (male ++ proj₂ (subterm seed B N female))
