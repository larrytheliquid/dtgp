module Stash where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec

infixr 2 _∶_∣_

data Word : Set where
  Exec-STACKDEPTH Exec-DUP Exec-EQ Exec-ROT
    Exec-SWAP Exec-K Exec-S Exec-POP
    true false Bool-POP AND NOT
    Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : ℕ → Set
Term n = Vec Word n

data _∶_∣_ : ∀ {n} (t : Term n) (Bool Nat : ℕ) → Set where
  empty : [] ∶ 0 ∣ 0

  Exec-STACKDEPTH : ∀ {n B N} {t : Term n} →
                      t ∶ B ∣ N →
    Exec-STACKDEPTH ∷ t ∶ B ∣ suc N

  Exec-DUP : ∀ {n B N w} {t : Term n} →
           w ∷ w ∷ t ∶ B ∣ N →
    Exec-DUP ∷ w ∷ t ∶ B ∣ N

  Exec-EQ : ∀ {n B N w₁ w₂} {t : Term n} →
                       t ∶     B ∣ N →
    Exec-EQ ∷ w₁ ∷ w₂ ∷ t ∶ suc B ∣ N

  Exec-ROT : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
               w₃ ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N →
    Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-SWAP : ∀ {n B N w₁ w₂} {t : Term n} →
                w₂ ∷ w₁ ∷ t ∶ B ∣ N →
    Exec-SWAP ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-K : ∀ {n B N w₁ w₂} {t : Term n} →
                 w₁ ∷ t ∶ B ∣ N →
    Exec-K ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-S : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
  -- TODO: confirm with old w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B ∣ N →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B ∣ N →
    Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-POP : ∀ {n B N w} {t : Term n} →
                   t ∶ B ∣ N →
    Exec-POP ∷ w ∷ t ∶ B ∣ N

  true : ∀ {n B N} {t : Term n} →
           t ∶     B ∣ N →
    true ∷ t ∶ suc B ∣ N

  false : ∀ {n B N} {t : Term n} →
            t ∶     B ∣ N →
    false ∷ t ∶ suc B ∣ N

  Bool-POP : ∀ {n B N} {t : Term n} →
               t ∶ suc B ∣ N →
    Bool-POP ∷ t ∶     B ∣ N

  AND : ∀ {n B N} {t : Term n} →
          t ∶ suc (suc B) ∣ N →
    AND ∷ t ∶      suc B  ∣ N

  NOT : ∀ {n B N} {t : Term n} →
          t ∶ suc B ∣ N →
    NOT ∷ t ∶ suc B ∣ N

  nat : ∀ {n B N v} {t : Term n} →
            t ∶ B ∣     N →
    nat v ∷ t ∶ B ∣ suc N

  Nat-POP : ∀ {n B N} {t : Term n} →
              t ∶ B ∣ suc N →
    Nat-POP ∷ t ∶ B ∣     N

  ADD : ∀ {n B N} {t : Term n} →
          t ∶ B ∣ suc (suc N) →
    ADD ∷ t ∶ B ∣      suc N

  LT : ∀ {n B N} {t : Term n} →
         t ∶     B ∣ suc (suc N) →
    LT ∷ t ∶ suc B ∣          N

  GT : ∀ {n B N} {t : Term n} →
         t ∶     B ∣ suc (suc N) →
    GT ∷ t ∶ suc B ∣          N

Well : {n B N : ℕ} → Term n → Set
Well {B = B} {N = N} t = t ∶ B ∣ N

Ill : {n B N : ℕ} → Term n → Set
Ill {B = B} {N = N} t = ¬ Well {B = B} {N = N} t

data Typed {n} (t : Term n) : Set where
  well : ∀ {B N} → Well {B = B} {N = N} t → Typed t
  ill  : Typed t
