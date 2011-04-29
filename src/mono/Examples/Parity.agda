module Examples.Parity where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.List hiding (and; or; sum; map; [_])
open import Data.Vec hiding (init)
import DTGP

data Word : Set where
  not and or : Word

pre : Word → ℕ → ℕ
pre not n = 1 + n
pre and n = 2 + n
pre or  n = 2 + n

post : Word → ℕ → ℕ
post not n = 1 + n
post and n = 1 + n
post or  n = 1 + n

even : ℕ → Bool
even zero = true
even (suc zero) = false
even (suc (suc zero)) = true
even (suc n) = even n

trues : ∀ {n} → Vec Bool n → ℕ
trues [] = 0
trues (true ∷ xs) = suc (trues xs)
trues (false ∷ xs) = trues xs

evenParity : ∀ {n} → Vec Bool n → Bool
evenParity xs = even (trues xs)

open DTGP Word pre post

eval : ∀ {inp out} → Term inp out → Vec Bool inp → Vec Bool out
eval [] is = is
eval (not ∷ xs) is with eval xs is
... | o ∷ os = Data.Bool.not o ∷ os
eval (and ∷ xs) is with eval xs is
... | o₂ ∷ o₁ ∷ os = (o₁ ∧ o₂) ∷ os
eval (or ∷ xs) is with eval xs is
... | o₂ ∷ o₁ ∷ os = (o₁ ∨ o₂) ∷ os

bitEqual : ∀ {m n} → Vec Bool m → Vec Bool n → Bool
bitEqual [] [] = true
bitEqual (_ ∷ _) [] = false
bitEqual [] (_ ∷ _) = false
bitEqual (x ∷ xs) (y ∷ ys) = x ∧ y ∧ bitEqual xs ys

scores : ∀ {inp out n} → Vec (Vec Bool inp) n → Term inp out → ℕ
scores ass xs = sum (map (λ as →
  if (bitEqual (eval xs as) [ evenParity as ])
  then 1 else 0)
  ass)

fitnessCases : Vec (Vec Bool _) _
fitnessCases =
    (true ∷ true ∷ [])
  ∷ (true ∷ false ∷ [])
  ∷ (false ∷ true ∷ [])
  ∷ (false ∷ false ∷ [])
  ∷ []

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc m == suc n = m == n

score : Term _ _ → ℕ
score xs = scores fitnessCases xs

open Evolution score

match : (w : Word) (out : ℕ) → Dec (∃ λ n → out ≡ pre w n)
match not zero = no ¬p where
  ¬p : Σ ℕ (λ n → 0 ≡ suc n) → ⊥
  ¬p (_ , ())
match not (suc n) = yes (n , refl)
match and zero = no ¬p where
  ¬p : Σ ℕ (λ n → 0 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match and (suc zero) = no ¬p where
  ¬p : Σ ℕ (λ n → 1 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match and (suc (suc n)) = yes (n , refl)
match or zero = no ¬p where
  ¬p : Σ ℕ (λ n → 0 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match or (suc zero) = no ¬p where
  ¬p : Σ ℕ (λ n → 1 ≡ suc (suc n)) → ⊥
  ¬p (_ , ())
match or (suc (suc n)) = yes (n , refl)

open Initialization match

choices : List Word
choices = not ∷ and ∷ or ∷ []

population : Population _ _ _
population = fromList (init 4 2 1 choices)

answer : Population _ _ _
answer = evolve 1337 1 population

