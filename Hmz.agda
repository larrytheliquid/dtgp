module Hmz where
open import Data.Nat

infixl 2 _⟶_
infixr 5 _,_∷_ -- _++_

-- data _⟶_ : ℕ → ℕ → Set where
--   []  : 0 ⟶ 0

--   _,_∷_ : ∀ {B B'} →
--     (inp out : ℕ) → (t : B ⟶ B') →
--     B + (inp ∸ B') ⟶ out + (B' ∸ inp)

-- data _⟶_ : ℕ → ℕ → Set where
--   []  : 0 ⟶ 0

--   _∷_ : ∀ {A out} →
--     (B : ℕ) → (t : A ⟶ out) → A ⟶ B

-- _++_ : ∀ {A B out} →
--   A ⟶ out → out ⟶ B → A ⟶ B
-- [] ++ ys = ys
-- (.0 ∷ t) ++ [] = {!!}
-- _++_ {A} {B} {out} (.out ∷ xs) (.B ∷ ys) = {!!}
-- --   with xs ++ (out ∷ ys)
-- -- ... | ih = ?

data _⟶_ : ℕ → ℕ → Set where
  []  : 0 ⟶ 0

  _,_∷_ : ∀ {B B'} →
    (delta-in delta-out : ℕ) →
    (t : B ⟶ B') →
    delta-in + B ⟶ B' + delta-out

_++_ : ∀ {A B out} →
  A ⟶ A' → B ⟶ B' →
  B + (In w ∸ B') ⟶ Out w + (B' ∸ In w)
[] ++ ys = {!!}
(delta-in , delta-out ∷ t) ++ ys
  = {!!}

-- _++_ : ∀ {A B out} →
--   A ⟶ out → out ⟶ B → A ⟶ B
-- [] ++ ys = {!!}
-- (delta-in , delta-out ∷ t) ++ ys
--   = {!!}
