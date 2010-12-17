module Hm where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils

postulate
  lem : ∀ {n} {t : Term n} →
    Typed (reverse t) → (w : Word) → Typed (reverse (w ∷ t))

try : ∀ {n} (t : Term n) → Typed (reverse t)
try [] = well empty
try (Exec-STACKDEPTH ∷ t) = {!!}
try (Exec-DUP ∷ t) = {!!}
try (Exec-EQ ∷ t) = {!!}
try (Exec-ROT ∷ t) = {!!}
try (Exec-SWAP ∷ t) = {!!}
try (Exec-K ∷ t) = {!!}
try (Exec-S ∷ t) = {!!}
try (Exec-POP ∷ t) = {!!}
try (true ∷ []) = well (true empty)
try (true ∷ t) with try t
... | well p = well (lem p true)
... | ill = ill
try (false ∷ t) = {!!}
try (Bool-POP ∷ t) = {!!}
try (AND ∷ t) = {!!}
try (NOT ∷ t) = {!!}
try (Nat-POP ∷ t) = {!!}
try (ADD ∷ t) = {!!}
try (LT ∷ t) = {!!}
try (GT ∷ t) = {!!}
try (nat v ∷ t) = {!!}
