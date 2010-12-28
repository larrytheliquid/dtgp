module Crossover where
open import Relation.Nullary
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.List.All
open import Data.Vec
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
