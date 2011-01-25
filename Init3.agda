open import Data.Nat
module Init3 (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)
open import Data.List hiding (_++_)

infixr 5 _∷_ _++_

data Term (A : ℕ) : ℕ → Set where
  []  : Term A A

  _∷_ : ∀ {n} →
    (w : W) → Term A (In w n) →
    Term A (Out w n)

_++_ : ∀ {A B C} →
  Term B C →
  Term A B →
  Term A C
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

ext : {A B B' C' : ℕ} → (C : ℕ) → Term B' C' → Term A B → Maybe (Term A C)
ext {B = B} {B' = B'} {C' = C'} C xs ys with C ≟ C' | B ≟ B'
... | yes p₁ | yes p₂ rewrite p₁ | p₂ = just (xs ++ ys)
... | _ | _ = nothing

exts : {A B : ℕ} → (C : ℕ) → List (∃₂ Term) → Term A B → List (Term A C)
exts C xss ys = gfilter (λ xs → ext C (proj₂ (proj₂ xs)) ys) xss

enum : ℕ → (A C : ℕ) → List (∃₂ Term) → List (Term A C)
enum zero A C xss with A ≟ C
... | no p = []
... | yes p rewrite p = [] ∷ []
enum (suc n) A C xss with enum n A C xss
... | ih = {!!}

