open import Relation.Binary
module Macro (S : Setoid) (W : Set) (Var : W → Set)
  (In Out : (w : W) → Var w → Setoid.carrier S)
  where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.Function
open import Data.Vec hiding (_++_)

open Setoid S

data Term (ins : carrier) : carrier → Set where
  nil  : ∀ {ins'} → ins ≈ ins' → Term ins ins'

  cons : ∀ {Inwv Outwv} (w : W) (v : Var w) →
    Inwv ≈ In w v →
    Outwv ≈ Out w v →
    Term ins Inwv →
    Term ins Outwv

append : ∀ {ins mids mids' outs} →
  mids ≈ mids' →
  Term mids' outs →
  Term ins mids →
  Term ins outs
append p (nil ins') ys = {!!}
append p (cons w v inwv outwv ws) ys =
  cons w v inwv outwv (append p ws ys)

-- nil ++ ys = ys
-- (cons x xs) ++ ys = cons x (xs ++ ys)

-- data Split {A C} B : Term A C → Set where
--   _++'_ :
--     (xs : Term B C)
--     (ys : Term A B) →
--     Split B (xs ++ ys)
