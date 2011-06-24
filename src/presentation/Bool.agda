module Bool where
open import Data.Nat
import DTGP

data Word : Set where
  true not and : Word

pre  : Word → ℕ → ℕ
pre  true  n =     n
pre  not   n = 1 + n
pre  and   n = 2 + n

post : Word → ℕ → ℕ
post true  n = 1 + n
post not   n = 1 + n
post and   n = 1 + n

open DTGP Word pre post
