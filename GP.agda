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

_∷ʳ_ : List A → A → List A
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

shift : List A → List A
shift [] = []
shift (x ∷ xs) = xs ∷ʳ x

shifts : ℕ → List A → List (List A)
shifts zero xs = []
shifts (suc n) xs with shift xs
... | next = next ∷ shifts n next

enumerations-of : ℕ → List A → List (List A)
enumerations-of n xs =
  concat (map (combinations-of n) 
              (shifts (length xs) xs))
