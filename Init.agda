open import Data.Nat
module Init (W : Set) (In Out : W → ℕ → ℕ) where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_; concat; map; init)
open import Data.List renaming (_++_ to _l++_)

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

toMaybe : {x y : ℕ} → Dec (x ≡ y) → Maybe ℕ
toMaybe (no p) = nothing
toMaybe {y = y} (yes p) = just y

dfilter : ∀ {A B} → (A → Dec B) → List A → List B
dfilter fdec []       = []
dfilter fdec (x ∷ xs) with fdec x
... | yes p = p ∷ dfilter fdec xs
... | no p = dfilter fdec xs

postulate
  match : (w : W) (out : ℕ) → ∃ λ k → Dec (out ≡ In w k)

unify : ∀ {w k inp out} →
  Term inp out →
  Dec (out ≡ In w k) →
  Maybe (Term inp (Out w k))
unify {w = w} {k = k} ws (no p) = nothing
unify {w = w} {k = k} ws (yes p)
  rewrite p = just (w ∷ ws)

tableize : (i A : ℕ) → List W → List (∃ (Term A))
tableize zero A ws = gfilter (λ w →
  maybe (λ t → just (_ , t)) nothing
    (unify [] (proj₂ (match w A)))
    ) ws
tableize (suc i) A ws
  with tableize i A ws
... | ih = concat (map (λ out,t → gfilter (λ w →
  maybe (λ t → just (_ , t)) nothing
    (unify (proj₂ out,t) (proj₂ (match w (proj₁ out,t))))
    ) ws) ih)

filterTo : ∀ {A} C → List (∃ (Term A)) → List (Term A C)
filterTo C [] = []
filterTo C ((C' , x) ∷ xs)
  with C' ≟ C
... | no p = filterTo C xs
... | yes p rewrite p = x ∷ filterTo C xs

init : (i A C : ℕ) → List W → List (Term A C)
init i A C ws = filterTo C (tableize i A ws)



