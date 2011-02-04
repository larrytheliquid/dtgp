module Init4e where
open import Data.Nat
open import Data.Maybe
open import Data.Product
import Init4

data Word : Set where
  true not and : Word

In : Word → ℕ
In true = 0
In not = 1
In and = 2

Out : Word → ℕ → ℕ
Out true n = 1 + n
Out not n = 1 + n
Out and n = 1 + n

open Init4 Word In Out

