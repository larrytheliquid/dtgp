module GP where
open import Data.Nat
open import Data.List

permutations : ∀ {A} → ℕ → List A → List (List A)
permutations 0 _ = [] ∷ []
permutations _ [] = []
permutations (suc n) (x ∷ xs) =
  (map (_∷_ x) (permutations n xs))
  ++
  (permutations (suc n) xs)

combinations : ∀ {A} → ℕ → List A → List (List A)
combinations zero xs = []
combinations (suc n) xs = permutations (suc n) xs ++ combinations n xs
