module Again where
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

greater-by : ∀ {m n} → Ordering m n → ℕ
greater-by (less _ _) = 0
greater-by (equal _) = 0
greater-by (greater _ k) = k

less-by : ∀ {m n} → Ordering m n → ℕ
less-by (less _ k) = k
less-by (equal _) = 0
less-by (greater _ _) = 0

infixl 2 _⟶_
data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  cons : ∀ {B B' In Out} →
    (ord : Ordering In B') →
    B ⟶ B' →
    greater-by ord + B ⟶ less-by ord + Out

compare' : ∀ {B B' In Out} →
  In ⟶ Out →
  B ⟶ B' →
  Ordering In B'
compare' {B' = B'} {In = In} _ _
  = compare In B'

append : ∀ {B B' In} Out →
  (ord : Ordering In B') →
  In ⟶ Out →
  B ⟶ B' →
  greater-by ord + B ⟶ less-by ord + Out
append .0 ord1 [] ys = {!!}
append .(less-by ord2 + Out) ord1 (cons {B0} {B1} {In} {Out} ord2 xs) ys
  with compare' xs ys
append .(less-by B' + B0) ord1 (cons {B'} {B0} ord2 xs) ys | less .B' k = {!!}
append .(less-by ord2 + Out) ord1 (cons {B} {B'} {Out = Out} ord2 xs) ys | equal ._
  with append _ (equal _) xs ys
... | ih with cons {Out = (less-by ord2 + Out)} ord2 ih
... | ret = {!!}
append ._ ord1 (cons ord2 xs) ys | greater ._ k = {!!}

-- append ord1 (cons ord2 xs) ys
--   with compare' xs ys
-- append ord1 (cons {B'} ord2 xs) ys | less ._ k = {!!}
-- append ord1 (cons ord2 xs) ys | equal ._
--   with append (equal _) xs ys
-- ... | ih = {!!}
-- -- with cons ord1 ih
-- -- ... | ret = {!!}
-- append ord1 (cons ord2 xs) ys | greater ._ k = {!!}
