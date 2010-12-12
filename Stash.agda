module Stash where
open import Relation.Nullary
open import Data.Nat
open import Data.Bool
open import Data.List

infixr 2 _∶_∣_

data Word : Set where
  Exec-POP true false Bool-POP AND NOT Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : Set
Term = List Word

data _∶_∣_ : (t : Term) (Bool Nat : ℕ) → Set where
  empty : [] ∶ 0 ∣ 0

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
Ill {B} {N} t = ¬ (t ∶ B ∣ N)

private
  eg-term : Term
  eg-term = AND ∷ true ∷ GT ∷ nat 4 ∷ nat 3 ∷ []

  eg-type : Well eg-term
  eg-type = AND (true (GT (nat (nat empty))))

  fix-term : Term
  fix-term = GT ∷ Exec-POP ∷ nat 3 ∷ []

  fix-type : Well fix-term
  fix-type = Exec-POP (nat empty)

  break-term : Term
  break-term = GT ∷ nat 4 ∷ Exec-POP ∷ nat 3 ∷ []

  break-type : ∀ N → Ill {N = N} break-term
  break-type _ (GT (Exec-POP (nat ())))
  break-type _ (GT (nat ()))

data Typed {B N} (t : Term) : Set where
  well : Well {B} {N} t → Typed t
  ill  : Ill  {B} {N} t → Typed t

