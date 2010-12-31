module Syntax where
open import Data.Nat
import Stash

data Word : Set where
  true false
    not and or 
    dup flush
    : Word

In : Word → ℕ → ℕ
In true  B = 0
In false B = 0
In not   B = 1
In and   B = 2
In or    B = 2
In dup   B = 1
In flush B = B

Out : Word → ℕ → ℕ
Out true  B = 1
Out false B = 1
Out not   B = 1
Out and   B = 1
Out or    B = 1
Out dup   B = 2
Out flush B = 0
