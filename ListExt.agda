module ListExt where
open import Data.Nat
open import Data.List

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
m ^ suc n = m * (m ^ n)

enumerates : ℕ → ℕ
enumerates n = suc (helper n n) where
  helper : ℕ → ℕ → ℕ
  helper m zero = 0
  helper m (suc n) = (m ^ suc n) + helper m n

enumerate-to : ∀ {A} → ℕ → List A → List (List A)
enumerate-to n xs = take n
  (concatMap (sequence monad) 
             (inits (replicate n xs)))

enumerate : ∀ {A} → List A → List (List A)
enumerate xs = enumerate-to (enumerates (length xs)) xs
