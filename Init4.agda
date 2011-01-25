open import Data.Nat
module Init4 (W : Set) (In Out : W → ℕ → ℕ) where
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

go : {b c : ℕ} (n a : ℕ) → Term b c → Maybe (Term a c)
go zero c xs = {!!}
go {b = b} (suc n) c xs with go n xs

-- go : (n a c : ℕ) → W → Maybe (Term a c)
-- go zero a c w with a ≟ c
-- ... | no p = nothing
-- ... | yes p rewrite p = just []
-- go (suc n) a c w with go n a (In w c w
