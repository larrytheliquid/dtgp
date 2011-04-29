module Stash.List where
open import Data.List hiding (gfilter)
open import Relation.Nullary

gfilter : {A B : Set} →
          (A → Dec B) → List A → List B
gfilter f []       = []
gfilter f (x ∷ xs) with f x
... | yes p = p ∷ gfilter f xs
... | no _ = gfilter f xs
