module Koza94 where
open import Data.Nat
open import Data.List hiding (and; or)
open import Data.Vec hiding (map)
open import Data.Product hiding (map)
open import ListExt
import Stash

data Word : Set where
  true false nand nor : Word

In : Word → ℕ → ℕ
In true  B = 0
In false B = 0
In nand  B = 2
In nor   B = 2

Out : Word → ℕ → ℕ
Out true  B = 1
Out false B = 1
Out nand  B = 1
Out nor   B = 1

open Stash Word In Out

raw-lang : List Word
raw-lang = true ∷ false ∷ nand ∷ nor ∷ []

raw-bank : List (List Word)
raw-bank = enumerate raw-lang

bank : Terms
bank = _ , fromList (map from-List raw-bank)
