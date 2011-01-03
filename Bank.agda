module Bank where
open import Data.Nat
open import Data.Vec
open import Data.Product
import Stash
open import Syntax
open Stash Word In Out

language : Term
language = _ , _ , true ∷ false ∷ not ∷ and ∷ or ∷ dup ∷ flush ∷ []

bank : Terms
bank = population language
