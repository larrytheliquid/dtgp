module Stash where
open import Data.Nat
open import Data.Bool
open import Data.List

infixr 2 _∶_∣_∣_

data Word : Set where
  Exec-POP true false Bool-POP AND NOT Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : Set
Term = List Word

data _∶_∣_∣_ (t : Term) : (Exec : Term) (Bool Nat : ℕ) → Set where
  push : t ∶ t ∣ 0 ∣ 0

  Exec-POP : ∀ {w E B N} →
    t ∶ Exec-POP ∷ w ∷ E ∣ B ∣ N →
    t ∶ E ∣ B ∣ N

  true : ∀ {E B N} →
    t ∶ true ∷ E ∣ B ∣ N →
    t ∶ E ∣ suc B ∣ N

  false : ∀ {E B N} →
    t ∶ false ∷ E ∣ B ∣ N →
    t ∶ E ∣ suc B ∣ N

  Bool-POP : ∀ {E B N} →
    t ∶ Bool-POP ∷ E ∣ suc B ∣ N →
    t ∶ E ∣ B ∣ N

  AND : ∀ {E B N} →
    t ∶ AND ∷ E ∣ suc (suc B) ∣ N →
    t ∶ E ∣ suc B ∣ N

  NOT : ∀ {E B N} →
    t ∶ NOT ∷ E ∣ suc B ∣ N →
    t ∶ E ∣ suc B ∣ N

  nat : ∀ {E B N n} →
    t ∶ (nat n) ∷ E ∣ B ∣ N →
    t ∶ E ∣ B ∣ suc N

  Nat-POP : ∀ {E B N} →
    t ∶ Nat-POP ∷ E ∣ B ∣ suc N →
    t ∶ E ∣ B ∣ N

  ADD : ∀ {E B N} →
    t ∶ ADD ∷ E ∣ B ∣ suc (suc N) →
    t ∶ E ∣ B ∣ suc N

  LT : ∀ {E B N} →
    t ∶ LT ∷ E ∣ B ∣ suc (suc N) →
    t ∶ E ∣ suc B ∣ N

  GT : ∀ {E B N} →
    t ∶ GT ∷ E ∣ B ∣ suc (suc N) →
    t ∶ E ∣ suc B ∣ N

Well : {B N : ℕ} → Term → Set
Well {B} {N} t = t ∶ [] ∣ B ∣ N

private
  eg-term : Term
  eg-term = nat 3 ∷ nat 4 ∷ GT ∷ true ∷ AND ∷ []

  eg-type : Well eg-term
  eg-type = AND (true (GT (nat (nat push))))

  pop-term : Term
  pop-term = nat 3 ∷ Exec-POP ∷ GT ∷ []

  pop-type : Well pop-term
  pop-type = Exec-POP (nat push)

