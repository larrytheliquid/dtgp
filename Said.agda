module Said where
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

left : ℕ → ℕ → ℕ → ℕ
left In B' B with compare In B'
left In .(suc (In + k)) B | less .In k = B
left .B' B' B | equal .B' = B
left .(suc (B' + k)) B' B | greater .B' k = k + B

right : ℕ → ℕ → ℕ → ℕ
right B' In Out with compare B' In
right B' .(suc (B' + k)) Out | less .B' k = Out
right .In In Out | equal .In = Out
right .(suc (In + k)) In Out | greater .In k = k + Out

infixl 2 _⟶_
data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  cons : ∀ {B B'} →
    (In Out : ℕ) → Ordering  → B ⟶ B' →
    left In B' B ⟶ right B' In Out
    -- (In ∸ B') + B ⟶ (B' ∸ In) + Out

-- _++_ : ∀ {B B' In Out} →
--   In ⟶ Out → B ⟶ B' →
--   left In B' B ⟶ right B' In Out
-- [] ++ ys = {!!}
-- cons {B} {B'} In Out xs ++ ys
--   with compare In B'

-- cons In Out xs ++ ys | less .In k = {!!}

-- cons {B1} {B'} .B' Out xs ++ ys | equal .B'
--   with xs ++ ys
-- ... | ih with cons B' Out ih
-- ... | ret = {!!}

-- cons {B1} {B'} .(suc (B' + k)) Out xs ++ ys | greater .B' k = {!!}

-- _++_ : ∀ {B B' In Out} →
--   In ⟶ Out → B ⟶ B' →
--   left In B' B ⟶ right B' In Out
-- _++_ {B' = B'} {In = In} xs ys with compare In B'
-- _++_ {B} {.(suc (In + k))} {In} xs ys | less .In k = {!!}
-- [] ++ ys | equal .0 = {!!}
-- cons {B'} {B0} In Out xs ++ ys | equal ._
--   with xs ++ ys
-- ... | ih = {!!}

-- _++_ {B} {B'} xs ys | greater .B' k = {!!}

_++_ : ∀ {B B' In Out} →
  In ⟶ Out → B ⟶ B' →
  left In B' B ⟶ right B' In Out
_++_ {B} {B'} {In} {Out} xs ys with left In B' B
[] ++ ys | zero = {!!}
cons In Out y ++ ys | zero = {!!}
xs ++ ys | suc n = {!!}
