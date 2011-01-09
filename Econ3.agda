module Econ3 where
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

In : ℕ → ℕ → ℕ → ℕ
In new-in old-in old-out =
  (new-in ∸ old-out) + old-in

Out : ℕ → ℕ → ℕ → ℕ
Out new-out new-in old-out =
  (old-out ∸ new-in) + new-out

open import Data.List

Out-List : List (ℕ × ℕ) → ℕ
Out-List [] = 0
Out-List (_∷_ (B , B') xs) =
  Out B' B (Out-List xs)

In-List : List (ℕ × ℕ) → ℕ
In-List [] = 0
In-List (_∷_ (B , B') xs) =
  In B (In-List xs) (Out-List xs)

data Econ : List (ℕ × ℕ) → ℕ → ℕ → Set where
  []  : Econ [] 0 0
  cons : ∀ {xs} →
    (x : ℕ × ℕ) →
    Econ xs (In-List xs) (Out-List xs) →
    Econ (x ∷ xs) (In-List (x ∷ xs)) (Out-List ((x ∷ xs)))

append : ∀ {xs ys} → Econ xs (In-List xs) (Out-List xs) → Econ ys (In-List ys) (Out-List ys) →
  Econ (xs ++ ys) (In-List (xs ++ ys)) (Out-List (xs ++ ys))
append [] ys = ys
append (cons x xs) ys = cons x (append xs ys)
         
