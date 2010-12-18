module Term where
open import Data.Nat
open import Data.Vec

data Word : Set where
  Exec-STACKDEPTH Exec-DUP Exec-EQ Exec-ROT
    Exec-SWAP Exec-K Exec-S Exec-POP
    true false Bool-POP AND NOT
    Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : ℕ → Set
Term n = Vec Word n
