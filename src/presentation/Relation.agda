module Relation where
open import Data.Nat

data Term (inp : ℕ) : ℕ → Set where
  []   : Term inp inp
  true : {out : ℕ} →
    Term inp out  →
    Term inp (1 + out)
  not  : {out : ℕ} →
    Term inp (1 + out) →
    Term inp (1 + out)
  and  : {out : ℕ} →
    Term inp (2 + out) →
    Term inp (1 + out)
