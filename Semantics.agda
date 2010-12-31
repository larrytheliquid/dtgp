module Semantics where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Vec
import Stash
open import Syntax
open Stash Word In Out

private
  plus0 : ∀ n → n + 0 ≡ n
  plus0 zero = refl
  plus0 (suc n) with plus0 n
  ... | p rewrite p = refl

  plus1 : ∀ n → n + 1 ≡ suc n
  plus1 zero = refl
  plus1 (suc n) with plus1 n
  ... | p rewrite p = refl

  plus2 : ∀ n → n + 2 ≡ suc (suc n)
  plus2 zero = refl
  plus2 (suc n) with plus2 n
  ... | p rewrite p = refl

  0minus : ∀ n → 0 ∸ n ≡ 0
  0minus zero = refl
  0minus (suc n) = refl

  minus : ∀ n → n ∸ n ≡ 0
  minus zero = refl
  minus (suc n) = minus n

  lem : ∀ m n → m + (0 ∸ n) ≡ m
  lem m n rewrite 0minus n | plus0 m = refl

run : {B B' : ℕ} → B ⟶ B' → Vec Bool B → Vec Bool B'
run [] [] = []

run (_∷_ {zero} {n} true t) xs =
  true ∷ run t []
run (_∷_ {suc m} {n} true t) xs
  rewrite lem m n =
  true ∷ run t xs

run (_∷_ {zero} {n} false t) xs =
  false ∷ run t []
run (_∷_ {suc m} {n} false t) xs
  rewrite lem m n =
  false ∷ run t xs

run (_∷_ {zero} {suc n} not t) xs rewrite 0minus n
  with run t []
... | y ∷ ys = Data.Bool.not y ∷ ys
run (_∷_ {suc m} {suc n} not t) (x ∷ xs) rewrite lem m n =
  run t (Data.Bool.not x ∷ xs)
run (_∷_ {m} {zero} not t) xs rewrite plus1 m =
  Data.Bool.not (head xs) ∷ []

run (_∷_ {zero} {suc zero} and t) (x ∷ [])
  with run t []
... | y ∷ [] = x ∧ y ∷ []
run (_∷_ {zero} {suc (suc n)} and t) xs rewrite 0minus n
  with run t []
... | y₂ ∷ y₁ ∷ ys = y₁ ∧ y₂ ∷ ys
run (_∷_ {suc m} {suc zero} and t) (x ∷ xs) rewrite plus1 m
  with run t xs
... | y ∷ [] = x ∧ y ∷ []
run (_∷_ {suc m} {suc (suc n)} and t) xs
  rewrite lem m n
  with run t xs
... | y₂ ∷ y₁ ∷ ys = y₁ ∧ y₂ ∷ ys
run (_∷_ {m} {zero} and t) xs rewrite plus2 m =
  (head (tail xs)) ∧ (head xs) ∷ []

run (_∷_ {zero} {suc zero} or t) (x ∷ [])
  with run t []
... | y ∷ [] = (x ∨ y) ∷ []
run (_∷_ {zero} {suc (suc n)} or t) xs rewrite 0minus n
  with run t []
... | y₂ ∷ y₁ ∷ ys = (y₁ ∨ y₂) ∷ ys
run (_∷_ {suc m} {suc zero} or t) (x ∷ xs) rewrite plus1 m
  with run t xs
... | y ∷ [] = (x ∨ y) ∷ []
run (_∷_ {suc m} {suc (suc n)} or t) xs
  rewrite lem m n
  with run t xs
... | y₂ ∷ y₁ ∷ ys = (y₁ ∨ y₂) ∷ ys
run (_∷_ {m} {zero} or t) xs rewrite plus2 m =
  (head (tail xs) ∨ head xs) ∷ []

run (_∷_ {zero} {suc n} dup t) xs
  with run t []
... | y ∷ ys = y ∷ y ∷ ys
run (_∷_ {m} {zero} dup t) xs
  rewrite plus1 m
  = head xs ∷ head xs ∷ []
run (_∷_ {suc m} {suc n} dup t) (x ∷ xs)
  rewrite lem m n
  = x ∷ run t (x ∷ xs)

run (_∷_ {zero} {n} flush t) xs
  rewrite minus n
  = []
run (_∷_ {m} {n} flush t) xs
  rewrite minus n
  = []
