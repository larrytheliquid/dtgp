open import Data.Nat hiding (_≥_)
module DTGP (Word : Set) (pre post : Word → ℕ → ℕ) where
open import Data.Product

infixr 5 _∷_ _++_ _++'_

data Term (inp : ℕ) : ℕ → Set where
  []  : Term inp inp

  _∷_ : ∀ {n} (w : Word) →
    Term inp (pre w n) → Term inp (post w n)

_++_ : ∀ {inp mid out} →
  Term mid out →
  Term inp mid →
  Term inp out
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {inp out} mid : Term inp out → Set where
  _++'_ :
    (xs : Term mid out)
    (ys : Term inp mid) →
    Split mid (xs ++ ys)

split : ∀ {inp out} (n : ℕ) (xs : Term inp out) →
  Σ ℕ λ mid → Split mid xs
split zero xs = _ , [] ++' xs
split (suc n) [] = _ , [] ++' []
split (suc n) (x ∷ xs) with split n xs
split (suc n) (x ∷ ._) | _ , xs ++' ys = _ , (x ∷ xs) ++' ys
