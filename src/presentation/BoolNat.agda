module BoolNat where
open import Data.Nat renaming (_≟_ to _≟n_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary
import Poly

infixr 4 _,_

data Word : Set where
  not gt : Word
  num : ℕ → Word

record Domain : Set where
  constructor _,_
  field
    bools : ℕ
    nats : ℕ

postulate _≟_ : (x y : Domain) → Dec (x ≡ y)

pre : Word → Domain → Domain
pre not     (m , n) = 1 + m ,     n
pre (num _) (m , n) =     m ,     n
pre gt      (m , n) =     m , 2 + n

post : Word → Domain → Domain
post not     (m , n) = 1 + m ,     n
post (num _) (m , n) =     m , 1 + n
post gt      (m , n) = 1 + m ,     n

open Poly pre post _≟_

bc : Term (0 , 2) (1 , 0)
bc = not ∷ gt ∷ []

ab : Term (0 , 0) (0 , 2)
ab = num 3 ∷ num 5 ∷ []

ac : Term (0 , 0) (1 , 0)
ac = bc ++ ab


