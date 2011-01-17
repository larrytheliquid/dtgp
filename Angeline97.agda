module Angeline97 where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Vec
import Stashy

data Word : Set where
  not and or : Word

In : Word → ℕ → ℕ
In not n = 1
In and n = 2
In or  n = 2

Out : Word → ℕ → ℕ
Out not n = 1
Out and n = 1
Out or  n = 1

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc zero)) = true
even (suc n) = even n

trues : ∀ {n} → Vec Bool n → ℕ
trues [] = 0
trues (true ∷ xs) = suc (trues xs)
trues (false ∷ xs) = trues xs

evenParity : ∀ {n} → Vec Bool n → Bool
evenParity xs = even (trues xs)

open Stashy Word In Out

input : Vec Word 0
input = []

-- better?
