module Stash where
open import Relation.Nullary
open import Data.Nat
open import Data.Bool
open import Data.Vec

infixl 2 _∣_⊢_∶_∣_

data Word : Set where
  Exec-STACKDEPTH Exec-DUP Exec-EQ Exec-ROT
    Exec-SWAP Exec-K Exec-S Exec-POP
    true false Bool-POP AND NOT
    Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : ℕ → Set
Term n = Vec Word n

data _∣_⊢_∶_∣_ (Bool Nat : ℕ) : ∀ {n} (t : Term n) (B N : ℕ) → Set where
  empty : Bool ∣ Nat ⊢ [] ∶ Bool ∣ Nat

  Exec-POP : ∀ {n B N w} {t : Term n} →
                   Bool ∣ Nat ⊢ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-POP ∷ w ∷ t ∶ B ∣ N

  Exec-DUP : ∀ {n B N w} {t : Term n} →
           Bool ∣ Nat ⊢ w ∷ w ∷ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-DUP ∷ w ∷ t ∶ B ∣ N

  Exec-EQ : ∀ {n B N w₁ w₂} {t : Term n} →
                       Bool ∣ Nat ⊢ t ∶ suc B ∣ N →
    Bool ∣ Nat ⊢ Exec-EQ ∷ w₁ ∷ w₂ ∷ t ∶     B ∣ N

  Exec-K : ∀ {n B N w₁ w₂} {t : Term n} →
                 Bool ∣ Nat ⊢ w₁ ∷ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-K ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-SWAP : ∀ {n B N w₁ w₂} {t : Term n} →
                Bool ∣ Nat ⊢ w₂ ∷ w₁ ∷ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-SWAP ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N

  Exec-ROT : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
               Bool ∣ Nat ⊢ w₃ ∷ w₁ ∷ w₂ ∷ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-S : ∀ {n B N w₁ w₂ w₃} {t : Term n} →
        Bool ∣ Nat ⊢ w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B ∣ N →
    Bool ∣ Nat ⊢ Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t ∶ B ∣ N

  Exec-STACKDEPTH : ∀ {n B N} {t : Term n} →
                      Bool ∣ Nat ⊢ t ∶ B ∣ suc N →
    Bool ∣ Nat ⊢ Exec-STACKDEPTH ∷ t ∶ B ∣     N

  true : ∀ {n B N} {t : Term n} →
           Bool ∣ Nat ⊢ t ∶ suc B ∣ N →
    Bool ∣ Nat ⊢ true ∷ t ∶     B ∣ N

  false : ∀ {n B N} {t : Term n} →
            Bool ∣ Nat ⊢ t ∶ suc B ∣ N →
    Bool ∣ Nat ⊢ false ∷ t ∶     B ∣ N

  Bool-POP : ∀ {n B N} {t : Term n} →
               Bool ∣ Nat ⊢ t ∶     B ∣ N →
    Bool ∣ Nat ⊢ Bool-POP ∷ t ∶ suc B ∣ N

  AND : ∀ {n B N} {t : Term n} →
          Bool ∣ Nat ⊢ t ∶      suc B  ∣ N →
    Bool ∣ Nat ⊢ AND ∷ t ∶ suc (suc B) ∣ N

  NOT : ∀ {n B N} {t : Term n} →
          Bool ∣ Nat ⊢ t ∶ suc B ∣ N →
    Bool ∣ Nat ⊢ NOT ∷ t ∶ suc B ∣ N

  nat : ∀ {n B N v} {t : Term n} →
            Bool ∣ Nat ⊢ t ∶ B ∣ suc N →
    Bool ∣ Nat ⊢ nat v ∷ t ∶ B ∣     N

  Nat-POP : ∀ {n B N} {t : Term n} →
              Bool ∣ Nat ⊢ t ∶ B ∣     N →
    Bool ∣ Nat ⊢ Nat-POP ∷ t ∶ B ∣ suc N

  ADD : ∀ {n B N} {t : Term n} →
          Bool ∣ Nat ⊢ t ∶ B ∣      suc N →
    Bool ∣ Nat ⊢ ADD ∷ t ∶ B ∣ suc (suc N)

  LT : ∀ {n B N} {t : Term n} →
         Bool ∣ Nat ⊢ t ∶ suc B ∣          N →
    Bool ∣ Nat ⊢ LT ∷ t ∶     B ∣ suc (suc N)

  GT : ∀ {n B N} {t : Term n} →
         Bool ∣ Nat ⊢ t ∶ suc B ∣          N →
    Bool ∣ Nat ⊢ GT ∷ t ∶     B ∣ suc (suc N)

Well : {n : ℕ} → Term n → Set
Well t = ∀ {Bool Nat} → Bool ∣ Nat ⊢ t ∶ 0 ∣ 0

Ill : {n : ℕ} → Term n → Set
Ill t = ¬ Well t

data Typed {n} (t : Term n) (B N : ℕ) : Set where
  well : ∀ {Bool Nat} → Bool ∣ Nat ⊢ t ∶ B ∣ N → Typed t B N
  ill  : Typed t B N
