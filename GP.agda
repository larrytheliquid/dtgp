module GP (A : Set) where
open import Data.Nat
open import Data.List

combinations-of : ℕ → List A → List (List A)
combinations-of zero _ = [] ∷ []
combinations-of _ [] = []
combinations-of (suc n) (x ∷ xs) =
  map (_∷_ x) (combinations-of n xs)
  ++
  (combinations-of (suc n) xs)

repliconcat : ℕ → List A → List A
repliconcat n xs = concat (map (replicate n) xs)

enumeration-of : ℕ → List A → List (List A)
enumeration-of n xs = combinations-of n (repliconcat n xs)

enumerate : ℕ → List A → List (List A)
enumerate zero xs = [] ∷ []
enumerate (suc n) xs =
  enumeration-of (suc n) xs
  ++
  enumerate n xs

