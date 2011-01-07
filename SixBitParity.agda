module SixBitParity where
open import Data.Nat
import Stash

data Word : Set where
  d0 d1 d2 d3 d4 d5
    and or nand nor
    : Word

In : Word → ℕ → ℕ
In and  B = 2 + B
In or   B = 2 + B
In nand B = 2 + B
In nor  B = 2 + B
In _    B = B

Out : Word → ℕ → ℕ
Out _ B = 1 + B

open Stash Word In Out


