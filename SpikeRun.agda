module SpikeRun where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Vec
import Spike

data Word : Set where
  true not and dup flush : Word

In : Word → ℕ → ℕ
In true  B = 0
In not   B = 1
In and   B = 2
In dup   B = 1
In flush B = B

Out : Word → ℕ → ℕ
Out true  B = 1
Out not   B = 1
Out and   B = 1
Out dup   B = 2
Out flush B = 0

open Spike Word In Out

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

  lem : ∀ m n → m + (0 ∸ n) ≡ m
  lem m n rewrite 0minus n | plus0 m = refl

run : {B B' : ℕ} → B ⟶ B' → Vec Bool B → Vec Bool B'
run Spike.[] [] = []

run (Spike._∷_ {zero} {n} true t) xs =
  true ∷ run t []
run (Spike._∷_ {suc m} {n} true t) xs
  rewrite lem m n =
  true ∷ run t xs

run (Spike._∷_ {zero} {suc n} not t) xs rewrite 0minus n
  with run t []
... | y ∷ ys = Data.Bool.not y ∷ ys
run (Spike._∷_ {suc m} {suc n} not t) (x ∷ xs) rewrite lem m n =
  run t (Data.Bool.not x ∷ xs)
run (Spike._∷_ {m} {zero} not t) xs rewrite plus1 m =
  Data.Bool.not (head xs) ∷ []

run (Spike._∷_ {zero} {suc zero} and t) (x ∷ [])
  with run t []
... | y ∷ [] = x ∧ y ∷ []
run (Spike._∷_ {zero} {suc (suc n)} and t) xs rewrite 0minus n
  with run t []
... | y₂ ∷ y₁ ∷ ys = y₁ ∧ y₂ ∷ ys
run (Spike._∷_ {suc m} {suc zero} and t) (x ∷ xs) rewrite plus1 m
  with run t xs
... | y ∷ [] = x ∧ y ∷ []
run (Spike._∷_ {suc m} {suc (suc n)} and t) xs
  rewrite lem m n
  with run t xs
... | y₂ ∷ y₁ ∷ ys = y₁ ∧ y₂ ∷ ys
run (Spike._∷_ {m} {zero} and t) xs rewrite plus2 m =
  (head (tail xs)) ∧ (head xs) ∷ []

run (Spike._∷_ dup t) xs = {!!}

run (Spike._∷_ flush t) xs = {!!}
