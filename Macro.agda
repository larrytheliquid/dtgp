open import Relation.Binary
module Macro (S : Setoid) (W : Set) (Var : W → Set)
  (In Out : (w : W) → Var w → Setoid.carrier S)
  where
open import Data.Nat.DivMod
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (trans; refl; sym)
import Relation.Binary.EqReasoning as EqR; open EqR S
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
append p (nil ins') ys = rewrite' (trans p ins') ys
  where
  rewrite' : ∀ {ins mids outs} → mids ≈ outs → Term ins mids → Term ins outs
  rewrite' p (nil p') = nil (trans p' p)
  rewrite' p (cons w v inwv outwv ws) =
    cons w v inwv (trans (sym p) outwv) (rewrite' refl ws)
append p (cons w v inwv outwv ws) ys =
  cons w v inwv outwv (append p ws ys)
