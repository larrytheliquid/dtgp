module Expanded where
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Term

infixl 2 _∶_∣_

data _∶_∣_ : ∀ {n} (t : Term n) (Bool Nat : ℕ) → Set where
  empty : [] ∶ 0 ∣ 0

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

data Typed {n} (t : Term n) : Set where
  well : ∀ {B N} → t ∶ B ∣ N → Typed t
  ill  : Typed t

check' : ∀ {n} {t : Term n} → Typed t → (w : Word) → Typed (w ∷ t)
check' (well p) true = well (true p)
check' (well p) false = well (false p)
check' (well {B = suc (suc _)} p) Bool-POP = well (Bool-POP p)
check' (well {B = suc (suc _)} p) AND = well (AND p)
check' (well {B = suc _} p) NOT = well (NOT p)
check' (well {N = suc (suc _)} p) Nat-POP = well (Nat-POP p)
check' (well {N = suc (suc _)} p) ADD = well (ADD p)
check' (well {N = suc (suc _)} p) LT = well (LT p)
check' (well {N = suc (suc _)} p) GT = well (GT p)
check' (well p) (nat _) = well (nat p)
check' _ _ = ill

check : ∀ {n} (t : Term n) → Typed t
check [] = well empty
check (w ∷ t) = check' (check t) w
