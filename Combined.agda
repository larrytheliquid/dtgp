module Combined where
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Maybe
open import Term

infixl 2 _∶_∣_

data _∶_∣_ : ∀ {n} (t : Term n) (Bool Nat : ℕ) → Set where
  empty : ∀ {B N} → [] ∶ B ∣ N

  Exec-POP : ∀ {n B N w} {t : Term n} →
                   t ∶ B ∣ N →
    Exec-POP ∷ w ∷ t ∶ B ∣ N

  Exec-DUP : ∀ {n B N w} {t : Term n} →
           w ∷ w ∷ t ∶ B ∣ N →
    Exec-DUP ∷ w ∷ t ∶ B ∣ N

  Exec-EQ : ∀ {n B N w₁ w₂} {t : Term n} →
                       t ∶ suc B ∣ N →
    Exec-EQ ∷ w₁ ∷ w₂ ∷ t ∶     B ∣ N

  Exec-K : ∀ {n B N w₁ w₂} {t : Term n} →
                 w₁ ∷ t ∶ B ∣ N →
    Exec-K ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-SWAP : ∀ {n B N w₁ w₂} {t : Term n} →
                w₂ ∷ w₁ ∷ t ∶ B ∣ N →
    Exec-SWAP ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-ROT : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
               w₃ ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N →
    Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-S : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B ∣ N →
    Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-STACKDEPTH : ∀ {n B N} {t : Term n} →
                      t ∶ B ∣ suc N →
    Exec-STACKDEPTH ∷ t ∶ B ∣     N

  true : ∀ {n B N} {t : Term n} →
           t ∶ suc B ∣ N →
    true ∷ t ∶     B ∣ N

  false : ∀ {n B N} {t : Term n} →
            t ∶ suc B ∣ N →
    false ∷ t ∶     B ∣ N

  Bool-POP : ∀ {n B N} {t : Term n} →
               t ∶     B ∣ N →
    Bool-POP ∷ t ∶ suc B ∣ N

  AND : ∀ {n B N} {t : Term n} →
          t ∶      suc B  ∣ N →
    AND ∷ t ∶ suc (suc B) ∣ N

  NOT : ∀ {n B N} {t : Term n} →
          t ∶ suc B ∣ N →
    NOT ∷ t ∶ suc B ∣ N

  nat : ∀ {n B N v} {t : Term n} →
            t ∶ B ∣ suc N →
    nat v ∷ t ∶ B ∣     N

  Nat-POP : ∀ {n B N} {t : Term n} →
              t ∶ B ∣     N →
    Nat-POP ∷ t ∶ B ∣ suc N

  ADD : ∀ {n B N} {t : Term n} →
          t ∶ B ∣      suc N →
    ADD ∷ t ∶ B ∣ suc (suc N)

  LT : ∀ {n B N} {t : Term n} →
         t ∶ suc B ∣          N →
    LT ∷ t ∶     B ∣ suc (suc N)

  GT : ∀ {n B N} {t : Term n} →
         t ∶ suc B ∣          N →
    GT ∷ t ∶     B ∣ suc (suc N)

Well : {n : ℕ} → Term n → Set
Well t = t ∶ 0 ∣ 0

Ill : {n : ℕ} → Term n → Set
Ill t = ¬ Well t

data Typed {n} (t : Term n) : Set where
  well : Well t → Typed t
  ill  : Typed t
