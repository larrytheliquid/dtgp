open import Data.Nat
module Init2 (W : Set) (In Out : W → ℕ → ℕ) where
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

ext : {A B B' C : ℕ} → Term B' C → Term A B → Maybe (Term A C)
ext {B = B} {B' = B'} xs ys with B ≟ B'
... | yes p rewrite p = just (xs ++ ys)
... | no p = nothing

extp : {A B : ℕ} → Term A B → ∃₂ Term → Maybe (∃ λ C → Term A C)
extp ys (_ , _ , xs) with ext xs ys
... | just zs = just (_ , zs)
... | nothing = nothing

enum : {A B : ℕ} → List (∃₂ Term) → Term A B → List (∃ λ C → Term A C)
enum xss ys = gfilter (extp ys) xss

enums : {A B : ℕ} → List (∃₂ Term) → List (Term A B) → List (∃ λ C → Term A C)
enums xss yss = concatMap (enum xss) yss

