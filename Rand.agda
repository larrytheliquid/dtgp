module Rand where
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)

multiplier  = 25173
incrementer = 13849
modulus     = 65536

nextRand : ℕ → ℕ
nextRand n = toℕ ((n * multiplier + incrementer) mod modulus)
