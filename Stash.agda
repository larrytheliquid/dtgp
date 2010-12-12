module Stash where
open import Relation.Nullary
open import Data.Nat
open import Data.Bool
open import Data.List

infixr 2 _∶_∣_

data Word : Set where
  Exec-ROT Exec-SWAP Exec-POP
    true false Bool-POP AND NOT
    Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : Set
Term = List Word

data _∶_∣_ : (t : Term) (Bool Nat : ℕ) → Set where
  empty : [] ∶ 0 ∣ 0

  Exec-ROT : ∀ {t B N w₁ w₂ w₃ B₂ N₂} →
                          t ∶ B ∣ N →
                w₂ ∷ w₁ ∷ w₃ ∷ t ∶ B₂ ∣ N₂ →
    w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t ∶ B₂ ∣ N₂

  Exec-SWAP : ∀ {t B N w₁ w₂ B₂ N₂} →
                          t ∶ B ∣ N →
                w₁ ∷ w₂ ∷ t ∶ B₂ ∣ N₂ →
    w₂ ∷ w₁ ∷ Exec-SWAP ∷ t ∶ B₂ ∣ N₂

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
  eg-term = AND ∷ true ∷ GT ∷ nat 4 ∷ nat 7 ∷ []

  eg-type : Well eg-term
  eg-type = AND (true (GT (nat (nat empty))))

  fix-term : Term
  fix-term = GT ∷ Exec-POP ∷ nat 7 ∷ []

  fix-type : Well fix-term
  fix-type = Exec-POP (nat empty)

  break-term : Term
  break-term = GT ∷ nat 4 ∷ Exec-POP ∷ nat 7 ∷ []

  break-type : ∀ N → Ill {N = N} break-term
  break-type _ (GT (Exec-POP (nat ())))
  break-type _ (GT (nat ()))

  swap-term : Term
  swap-term = nat 2 ∷ nat 3 ∷ Exec-SWAP ∷ nat 1 ∷ []

  swap-type : Well swap-term
  swap-type = Exec-SWAP one (nat (nat one))
    where
    one : Well (nat 1 ∷ [])
    one = nat empty

  good-swap-term : Term
  good-swap-term = GT ∷ NOT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  good-swap-type : Well good-swap-term
  good-swap-type = Exec-SWAP two (NOT (GT two))
    where
    two : Well (nat 2 ∷ nat 1 ∷ [])
    two = nat (nat empty)

  bad-swap-term : Term
  bad-swap-term = NOT ∷ GT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  bad-swap-type : ∀ B N → Ill {B = B} {N = N} bad-swap-term
  bad-swap-type .(suc (suc B)) N
    (Exec-SWAP (nat (nat empty)) (GT (NOT {.(nat 2 ∷ nat 1 ∷ [])} {B} (nat (nat ())))))
  bad-swap-type .(suc B) N
    (NOT {.(GT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ [])} {B} (GT ()))

  good-rot-term : Term
  good-rot-term = true ∷ AND ∷ false ∷ Exec-ROT ∷ []

  good-rot-type : Well good-rot-term
  good-rot-type = Exec-ROT empty p
    where
    p : Well (AND ∷ false ∷ true ∷ [])
    p = AND (false (true empty))

  bad-rot-term : Term
  bad-rot-term = AND ∷ false ∷ true ∷ Exec-ROT ∷ []

  bad-rot-type : ∀ B N → Ill {B = B} {N = N} bad-rot-term
  bad-rot-type .(suc (suc (suc B))) _ (Exec-ROT empty (false (true (AND {.[]} {B} ()))))
  bad-rot-type .(suc B) _ (AND {.(false ∷ true ∷ Exec-ROT ∷ [])} {B} (false (true ())))

data Typed {B N} (t : Term) : Set where
  well : Well {B} {N} t → Typed t
  ill  : Ill  {B} {N} t → Typed t

