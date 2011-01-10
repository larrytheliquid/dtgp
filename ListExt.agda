module ListExt where
open import Data.Nat
open import Data.List

enumerate : ∀ {A} → ℕ → List A → List (List A)
enumerate n xs = take n
  (concatMap (sequence monad) 
             (inits (replicate n xs)))
