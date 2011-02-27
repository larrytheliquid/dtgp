module Eg where
open import Data.Bool hiding (_≟_) renaming (not to ¬)
open import Data.Nat
open import Data.List hiding (_++_; and; or; concat; replicate)
open import Data.Vec hiding (init) renaming (_++_ to _v++_)
open import Data.Maybe
open import Data.Product hiding (swap)
open import Relation.Nullary hiding (¬_)
open import Relation.Binary.PropositionalEquality
import Init

data Word : Set where
  true false not and or dup swap pop square : Word

In : Word → ℕ → ℕ
In true n = n
In false n = n
In not n = 1 + n
In and n = 2 + n
In or n = 2 + n
In dup n = 1 + n
In swap n = 2 + n
In pop n = 1 + n
In square n = n

Out : Word → ℕ → ℕ
Out true n = 1 + n
Out false n = 1 + n
Out not n = 1 + n
Out and n = 1 + n
Out or n = 1 + n
Out dup n = 2 + n
Out swap n = 2 + n
Out pop n = n
Out square n = n * n

match : (w : Word) (out : ℕ) → ∃ λ k → Dec (out ≡ In w k)
match true n = n , yes refl
match false n = n , yes refl
match not zero = 0 , no λ()
match not (suc n) = n , yes refl
match and zero = 0 , no λ()
match and (suc zero) = 0 , no λ()
match and (suc (suc n)) = n , yes refl
match or zero = 0 , no λ()
match or (suc zero) = 0 , no λ()
match or (suc (suc n)) = n , yes refl
match dup zero = 0 , no λ()
match dup (suc n) = n , yes refl
match swap zero = 0 , no λ()
match swap (suc zero) = 0 , no λ()
match swap (suc (suc n)) = n , yes refl
match pop zero = 0 , no λ()
match pop (suc n) = n , yes refl
match square n = n , yes refl

open Init Word In Out

a : Term 3 3
a = []

b : Term 3 2
b = and ∷ a

c : Term 3 1
c = and ∷ b

bc : Term 2 1
bc = and ∷ []

ab : Term 3 2
ab = and ∷ []

abc : Term 3 1
abc = bc ++ ab

more : Term 6 5
more = and ∷ []

big : Term 10 8
big = (and ∷ []) ++ (and ∷ [])


eval : ∀ {A C} → Term A C → Vec Bool A → Vec Bool C
eval [] as = as
eval (true ∷ xs) as = true ∷ eval xs as
eval (false ∷ xs) as = false ∷ eval xs as
eval (not ∷ xs) as with eval xs as
... | c ∷ cs = ¬ c ∷ cs
eval (and ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∧ c₂) ∷ cs
eval (or ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ ∨ c₂) ∷ cs
eval (dup ∷ xs) as with eval xs as
... | c ∷ cs = c ∷ c ∷ cs
eval (swap ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = c₁ ∷ c₂ ∷ cs
eval (pop ∷ xs) as with eval xs as
... | c ∷ cs = cs
eval (_∷_ {n = n} square xs) as with eval xs as
... | cs = concat (replicate {n = n} cs)

open Initialization match

lang : List Word
lang = true ∷ not ∷ and ∷ []

gotry : List (Term 2 1)
gotry = init 4 2 1 lang



