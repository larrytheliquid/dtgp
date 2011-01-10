module Koza94 where
open import Data.Nat

data Word : Set where
  d0 d1 d2 d3 d4 d5
    and or
    nand nor
    : Word

In : Word → ℕ → ℕ
In and  B = 2
In or   B = 2
In nand B = 2
In nor  B = 2
In d*   B = 0

Out : Word → ℕ → ℕ
Out and  B = 1
Out or   B = 1
Out nand B = 1
Out nor  B = 1
Out d*   B = 1

