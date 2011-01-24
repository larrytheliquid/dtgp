open import Data.Nat
module Init (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)
open import Data.List hiding (_++_)

infixr 5 _∷_ _++_ -- _++'_

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

ext : {A B : ℕ} (n : ℕ) → Term A B → (w : W) → Maybe (Term A (Out w n))
ext {B = B} n xs x with B ≟ In x n
... | yes p rewrite p = just (x ∷ xs)
... | no p = nothing

extp : {A B : ℕ} (n : ℕ) → Term A B → W → Maybe (∃ λ w → Term A (Out w n))
extp n xs x with ext n xs x
... | just xxs = just (_ , xxs)
... | nothing = nothing

enum : {A B : ℕ} (n : ℕ) → Term A B → List W → List (∃ λ w → Term A (Out w n))
enum n xs ws = gfilter (extp n xs) ws

