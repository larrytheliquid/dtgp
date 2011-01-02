{-# OPTIONS --no-termination-check #-}
module Trash where
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Function

permutations : ∀ {A} → List A → List (List A)
permutations {A = A} xs0 = xs0 ∷ perms xs0 []
  where
  perms : List A → List A → List (List A)
  perms [] _ = []
  perms (t ∷ ts) is = foldr
    (λ xs r → proj₂ (interleave' id xs r))
    (perms ts (t ∷ is))
    (permutations is)
    where
    interleave' : (List A → List A) → List A → List (List A) → List A × List (List A)
    interleave' _ [] r = ts , r
    interleave' f (y ∷ ys) r with interleave' (f ∘ (_∷_ y)) ys r
    ... | us , zs = y ∷ us , f (t ∷ y ∷ us) ∷ zs



