module Rand where
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)
open import Data.Product

infixl 1 _>>=_

-- multiplier  = 25173
-- incrementer = 13849
-- modulus     = 65536

-- nextRand : ℕ → ℕ
-- nextRand n = toℕ ((n * multiplier + incrementer) mod modulus)

data State (S A : Set) : Set where
  state : (S → A × S) → State S A

runState : ∀ {S A} → State S A → S → A × S
runState (state f) = f

runRand :  ∀ {S A} → State S A → S → A
runRand st seed = proj₁ (runState st seed)

return : ∀ {S A} → A → State S A
return a = state (λ s → a , s)

_>>=_ : {S A B : Set} → State S A → (A → State S B) → State S B
state h >>= f = state λ s →
  let a,newState = h s
      stateg = f (proj₁ a,newState)
  in
  runState stateg (proj₂ a,newState)

open import Data.Nat

calcRand : ℕ → ℕ × ℕ
calcRand n = n * 2 , n + 1

rand : State ℕ ℕ
rand = state calcRand

Rand : Set → Set
Rand A = State ℕ A

twoRands : Rand (ℕ × ℕ)
twoRands =
  rand >>= λ a →
  rand >>= λ b →
  return (a , b)


