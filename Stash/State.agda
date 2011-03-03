module Stash.State where
open import Data.Product

infixl 1 _>>=_ _=<<_

data State (S A : Set) : Set where
  state : (S → A × S) → State S A

runState : ∀ {S A} → State S A → S → A × S
runState (state f) = f

return : ∀ {S A} → A → State S A
return a = state (λ s → a , s)

_>>=_ : {S A B : Set} → State S A → (A → State S B) → State S B
state h >>= f = state λ s →
  let a,newState = h s
      stateg = f (proj₁ a,newState)
  in
  runState stateg (proj₂ a,newState)

_=<<_ : {S A B : Set} → (A → State S B) → State S A → State S B
f =<< stateh = stateh >>= f

