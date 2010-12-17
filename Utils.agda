module Utils where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Stash

_lt_ : ℕ → ℕ → Bool
zero lt (suc n) = true
(suc n) lt (suc m) = n lt m
_ lt _ = false

_gt_ : ℕ → ℕ → Bool
(suc n) gt zero = true
(suc n) gt (suc m) = n gt m
_ gt _ = false

eq-Word : Word → Word → Bool
eq-Word Exec-DUP Exec-DUP = true
eq-Word Exec-EQ Exec-EQ = true
eq-Word Exec-ROT Exec-ROT = true
eq-Word Exec-SWAP Exec-SWAP = true
eq-Word Exec-K Exec-K = true
eq-Word Exec-S Exec-S = true
eq-Word Exec-POP Exec-POP = true
eq-Word true true = true
eq-Word false false = true
eq-Word Bool-POP Bool-POP = true
eq-Word AND AND = true
eq-Word NOT NOT = true
eq-Word Nat-POP Nat-POP = true
eq-Word ADD ADD = true
eq-Word LT LT = true
eq-Word GT GT = true
eq-Word (nat m) (nat n) with Data.Nat._≟_ m n
... | yes _ = true
... | no _ = false
eq-Word _ _ = false
