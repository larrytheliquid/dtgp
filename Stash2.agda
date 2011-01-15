open import Data.Nat
module Stash2 (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Function
open import Data.List hiding (_++_; [_]; tails; map; inits)

infixl 2 _⟶_
infixr 5 _∷_ _++_

data _⟶_ (B : ℕ) : ℕ → Set where
  []  : B ⟶ B

  _∷_ : ∀ {k} →
    (w : W) → B ⟶ In w k →
    B ⟶ Out w k

_++_ : ∀ {Inw Outw B} →
  Inw ⟶ Outw →
  B ⟶ Inw →
  B ⟶ Outw
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

Term : ℕ → Set
Term m = ∃ (_⟶_ m)

Terms : ℕ → Set
Terms m = List (Term m)

map : ∀ {m} → (Term m → Term m) → Terms m → Terms m
map f [] = []
map f (xs ∷ xss) = f xs ∷ map f xss

tails : ∀ {m} → Term m → Terms m
tails (n , []) = (n , []) ∷ []
tails (._ , x ∷ xs) =
  (_ , x ∷ xs) ∷ tails (_ , xs)

