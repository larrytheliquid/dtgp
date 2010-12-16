module Stash where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List

infixr 2 _∶_∣_

data Word : Set where
  Exec-DUP Exec-EQ Exec-ROT Exec-SWAP Exec-K Exec-S Exec-POP
    true false Bool-POP AND NOT
    Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : Set
Term = List Word

data _∶_∣_ : (t : Term) (Bool Nat : ℕ) → Set where
  empty : [] ∶ 0 ∣ 0

  Exec-DUP : ∀ {t B N w} →
           w ∷ w ∷ t ∶ B ∣ N →
    w ∷ Exec-DUP ∷ t ∶ B ∣ N

  Exec-EQ : ∀ {t B N w₁ w₂} →
                       t ∶     B ∣ N →
    w₂ ∷ w₁ ∷ Exec-EQ ∷ t ∶ suc B ∣ N

  Exec-ROT : ∀ {t B N w₁ w₂ w₃} →
               w₂ ∷ w₁ ∷ w₃ ∷ t ∶ B ∣ N →
    w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t ∶ B ∣ N

  Exec-SWAP : ∀ {t B N w₁ w₂} →
                w₁ ∷ w₂ ∷ t ∶ B ∣ N →
    w₂ ∷ w₁ ∷ Exec-SWAP ∷ t ∶ B ∣ N

  Exec-K : ∀ {t B N w₁ w₂} →
                 w₁ ∷ t ∶ B ∣ N →
    w₂ ∷ w₁ ∷ Exec-K ∷ t ∶ B ∣ N

  Exec-S : ∀ {t B N w₁ w₂ w₃} →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B ∣ N →
    w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t ∶ B ∣ N

  Exec-POP : ∀ {t B N w} →
                   t ∶ B ∣ N →
    w ∷ Exec-POP ∷ t ∶ B ∣ N

  true : ∀ {t B N} →
           t ∶     B ∣ N →
    true ∷ t ∶ suc B ∣ N

  false : ∀ {t B N} →
            t ∶     B ∣ N →
    false ∷ t ∶ suc B ∣ N

  Bool-POP : ∀ {t B N} →
               t ∶ suc B ∣ N →
    Bool-POP ∷ t ∶     B ∣ N

  AND : ∀ {t B N} →
          t ∶ suc (suc B) ∣ N →
    AND ∷ t ∶      suc B  ∣ N

  NOT : ∀ {t B N} →
          t ∶ suc B ∣ N →
    NOT ∷ t ∶ suc B ∣ N

  nat : ∀ {t B N n} →
            t ∶ B ∣     N →
    nat n ∷ t ∶ B ∣ suc N

  Nat-POP : ∀ {t B N} →
              t ∶ B ∣ suc N →
    Nat-POP ∷ t ∶ B ∣     N

  ADD : ∀ {t B N} →
          t ∶ B ∣ suc (suc N) →
    ADD ∷ t ∶ B ∣      suc N

  LT : ∀ {t B N} →
         t ∶     B ∣ suc (suc N) →
    LT ∷ t ∶ suc B ∣          N

  GT : ∀ {t B N} →
         t ∶     B ∣ suc (suc N) →
    GT ∷ t ∶ suc B ∣          N

Well : {B N : ℕ} → Term → Set
Well {B} {N} t = t ∶ B ∣ N

Ill : {B N : ℕ} → Term → Set
Ill {B} {N} t = ¬ Well {B} {N} t

data Typed (t : Term) : Set where
  well : ∀ {B N} → Well {B} {N} t → Typed t
  ill  : Typed t
