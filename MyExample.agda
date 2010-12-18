module MyExample where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Term
open import Combined

-- hm4 : NOT ∷ [] ∶ 0 ∣ 0
-- hm4 = NOT empty

-- hm5 : true ∷ AND ∷ false ∷ [] ∶ 0 ∣ 0
-- hm5 = true {!AND!}

hm2 : true ∷ [] ∶ 0 ∣ 0
hm2 = true empty

hm3 : true ∷ NOT ∷ [] ∶ 0 ∣ 0
hm3 = true (NOT empty)

hm4 : true ∷ false ∷ AND ∷ [] ∶ 0 ∣ 0
hm4 = true (false (AND empty))

-- bool-pop : true ∷ Bool-POP ∷ [] ∶ 0 ∣ 0
-- bool-pop = true (Bool-POP empty)

-- bool-pop : true ∷ Bool-POP ∷ false ∷ [] ∶ 0 ∣ 0
-- bool-pop = true (Bool-POP (false empty))

-- bool-pop : true ∷ false ∷ Bool-POP ∷ [] ∶ 0 ∣ 0
-- bool-pop = true (false (Bool-POP empty))

-- bool-pop : true ∷ false ∷ AND ∷ Bool-POP ∷ [] ∶ 0 ∣ 0
-- bool-pop = true (false (AND (Bool-POP empty)))

-- bool-pop : true ∷ false ∷ Bool-POP ∷ AND ∷ [] ∶ 0 ∣ 0 → ⊥
-- bool-pop (true (false (Bool-POP ())))
