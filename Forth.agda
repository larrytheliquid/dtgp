open import Data.Nat -- hiding (_∸_)
module Forth (W : Set) (In Out : W → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Function

-- infixl 6 _∸_
-- _∸_ : ℕ → ℕ → ℕ
-- suc m ∸ suc n = m ∸ n
-- zero  ∸ suc n = zero
-- m     ∸ zero  = m

infixl 2 _⟶_
infixr 5 _∷_

-- data _⟶_ : ℕ → ℕ → Set where
--   []  : 0 ⟶ 0

--   _∷_ : ∀ {B B'} →
--     (w : W) → B ⟶ B' →
--     (In w ∸ B') + B ⟶ (B' ∸ In w) + Out w

-- _v++_ : ∀ {A A' B B'} →
--   A ⟶ A' → B ⟶ B' →
--   A + (B ∸ A') ⟶ B' + (A' ∸ B)
-- [] v++ ys = {!!}
-- (x ∷ xs) v++ ys with xs v++ ys
-- ... | ih with x ∷ ih
-- ... | wut = {!!}

-- data _⟶_ : ℕ → ℕ → Set where
--   []  : 0 ⟶ 0

--   _∷_ : ∀ {B B'} →
--     (w : W) → B ⟶ B' →
--     B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)

-- _v++_ : ∀ {A A' B B'} →
--   A ⟶ A' → B ⟶ B' →
--   A + (B ∸ A') ⟶ B' + (A' ∸ B)
-- [] v++ ys = {!!}
-- (x ∷ xs) v++ ys with xs v++ ys
-- ... | ih with x ∷ ih
-- ... | wut = {!!}

lemmin : ∀ n → n ∸ n ≡ zero
lemmin zero = refl
lemmin (suc n) = lemmin n

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _∷_ : ∀ {B B'} →
    (w : W) → B ⟶ B' →
    (In w ∸ B') + B ⟶ (B' ∸ In w) + Out w

_v++_ : ∀ {B B' C C'} →
  C ⟶ C' → B ⟶ B' →
    (B ∸ C') + C ⟶ (C' ∸ B) + B'
_v++_ {B = B} {C' = C'} xs ys
  with compare B C'
... | comp  = {!!}

-- _v++_ : ∀ {B B' C C'} →
--   C ⟶ C' → B ⟶ B' →
--     (B ∸ C') + C ⟶ (C' ∸ B) + B'
-- match necessary ._ C' patterns from ∷
-- see by matching C' = C'
-- _v++_ {C' = ._} (_∷_ {B = B} {B' = B0} x xs) ys = {!!}

-- _v++_ {.C'} {B'} {C} {C'} xs ys | equal .C' 
--   rewrite lemmin C' = {!!}

-- _v++_ {B = B} {C' = C'} xs ys
--   with compare B C'
-- _v++_ {B} xs ys | less .B k = {!!}
-- [] v++ ys | equal .0 = {!!}
-- _∷_ {B} {B0} x xs v++ ys | equal .(B0 ∸ In x + Out x)
--   with xs v++ ys
-- ... | ih with x ∷ ih
-- ... | ret rewrite lemmin (B0 ∸ In x + Out x)
--   = {!!}
-- [] v++ ys | greater .0 k = {!!}
-- _∷_ {B} {B0} w y v++ ys | greater .(B0 ∸ In w + Out w) k = {!!}

-- _v++_ : ∀ {A A' B B'} →
--   A ⟶ A' → B ⟶ B' →
--   (B ∸ A') + A ⟶ (A' ∸ B) + B'
-- (x ∷ xs) v++ ys = {!!}
-- xs v++ ys = {!!}

-- _v++_ : ∀ {A A' B B'} →
--   A ⟶ A' → B ⟶ B' →
--   A + (B ∸ A') ⟶ B' + (A' ∸ B)
-- [] v++ ys = {!!}
-- (x ∷ xs) v++ ys with xs v++ ys
-- ... | ih with x ∷ ih
-- ... | wut = {!!}

-- -- In x ∸ (.B1 ∸ .B + .B') + (.B ∸ .B1 + .B0) ⟶
-- -- .B1 ∸ .B + .B' ∸ In x + Out x








-- -- Term : Set
-- -- Term = ∃₂ _⟶_

-- -- _++_ : ∀ {A A' B B'} →
-- --   A ⟶ A' → B ⟶ B' → Term
-- -- [] ++ ys = _ , _ , ys
-- -- (x ∷ xs) ++ ys with xs ++ ys
-- -- ... | _ , _ , ih = _ , _ , (x ∷ xs)

-- -- -- _v++_ : ∀ {A A' B B'} →
-- -- --   A ⟶ A' → B ⟶ B' →
-- -- --   B + (A ∸ B') ⟶ A' + (A' ∸ B)
-- -- -- [] v++ ys = {!!}
-- -- -- (x ∷ xs) v++ ys with xs v++ ys
-- -- -- ... | ih with x ∷ ih
-- -- -- ... | wut = {!!}

-- -- In-wtf : ∀ {B B'} → 
-- --   B ⟶ B' → ℕ
-- -- In-wtf [] = 0
-- -- In-wtf (w ∷ ws) = In w

-- -- Out-wtf : ∀ {B B'} → 
-- --   B ⟶ B' → ℕ
-- -- Out-wtf [] = 0
-- -- Out-wtf (w ∷ ws) = Out w

-- -- _wtf++_ : ∀ {A A' B B'} →
-- --   A ⟶ A' → (b : B ⟶ B') →
-- --   A + (In-wtf b ∸ A') ⟶ (Out-wtf b) + (A' ∸ In-wtf b)
-- -- [] wtf++ ys = {!!}
-- -- (x ∷ xs) wtf++ [] = {!!}
-- -- (x ∷ xs) wtf++ (y ∷ ys) with xs wtf++ (x ∷ ys)
-- -- ... | ih with x ∷ ih
-- -- ... | omg = {!!}

-- -- g++ : ∀ {A A' B B'} →
-- --   (w : W) →
-- --   A ⟶ A' →
-- --   -- A + (In w ∸ A') ⟶ Out w + (A' ∸ In w) →
-- --   B ⟶ B' →
-- --   (A + (In w ∸ A')) + (B ∸ (Out w + (A' ∸ In w))) ⟶ B' + ((Out w + (A' ∸ In w)) ∸ B)
-- -- g++ x [] ys = {!!}
-- -- g++ x (x' ∷ xs') ys with g++ x' xs' ys
-- -- ... | ih with x ∷ ih
-- -- ... | wtf = {!!}

-- -- -- B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)
-- -- -- .B0 + (.B ∸ .B1) ⟶ .B' + (.B1 ∸ .B)

-- -- -- lemma : ∀ {B B' Inw Outw} →
-- -- --   B + (Inw ∸ B') ⟶ Outw + (B' ∸ Inw) → ℕ
-- -- -- lemma (x ∷ xs) = {!!}

-- -- -- lemma : ∀ {B B' Inw Outw} (w : W) →
-- -- --   B + (Inw ∸ B') ⟶ Outw + (B' ∸ Inw) →
-- -- --   B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)
-- -- -- lemma w xs = {!!}

-- -- -- lemma : ∀ {B B' Inw Outw} (w : W) (ws : B ⟶ B') →
-- -- --   (B + (Inw ∸ B') ⟶ Outw + (B' ∸ Inw)) ∶ (w ∷ ws) →
-- -- --   B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)
-- -- -- lemma = ?


-- -- _s++_ : ∀ {A B Out} →
-- --   A   ⟶ Out →
-- --   Out ⟶ B →
-- --   A   ⟶ B
-- -- [] s++ ys = ys
-- -- (x ∷ xs) s++ ys with xs ++ ys
-- -- ... | a , b , zs = {!!}

-- -- _∷_++_ : ∀ {A A' B B'} →
-- --   (w : W) →
-- --   (ws : A ⟶ A') →
-- --   B ⟶ B' →
-- --   A + (B ∸ A') ⟶ B' + (A' ∸ B)
-- -- x ∷ xs ++ ys = {!!}
