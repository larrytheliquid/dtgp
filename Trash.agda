{-# OPTIONS --no-termination-check #-}
module Trash where
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Function

interleave' : ∀ {A} →
  A → List A → (List A → List A) → List A → List (List A) → List A × List (List A)
interleave' t ts _ [] r = ts , r
interleave' t ts f (y ∷ ys) r
  with interleave' t ts (f ∘ (_∷_ y)) ys r
... | us , zs = y ∷ us , f (t ∷ y ∷ us) ∷ zs

mutual
  permutations : ∀ {A} → List A → List (List A)
  permutations {A = A} xs0 = xs0 ∷ perms xs0 []

  perms : ∀ {A} → List A → List A → List (List A)
  perms [] _ = []
  perms (t ∷ ts) is = foldr
    (λ xs r → proj₂ (interleave' t ts id xs r))
    (perms ts (t ∷ is))
    (permutations is)




