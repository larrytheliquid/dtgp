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

Checks : Terms → ℕ → ℕ → Set
Checks ts B N = All (λ t → Typed (proj₂ t) B N) ts

subterms : ∀ {n} → Term n → Terms
subterms [] = []
subterms (t ∷ ts) with subterms ts
... | xs = (_ , t ∷ ts) ∷ xs

checks : (ts : Terms) (B N : ℕ) → Checks ts B N
checks [] B N = []
checks (t ∷ ts) B N = check' (proj₂ t) B N ∷ checks ts B N

