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

  Exec-DUP : ∀ {t B N w B₂ N₂} →
                   t ∶ B ∣ N →
           w ∷ w ∷ t ∶ B₂ ∣ N₂ →
    w ∷ Exec-DUP ∷ t ∶ B₂ ∣ N₂

  Exec-EQ : ∀ {t B N w₁ w₂} →
                       t ∶     B ∣ N →
    w₂ ∷ w₁ ∷ Exec-EQ ∷ t ∶ suc B ∣ N

  Exec-ROT : ∀ {t B N w₁ w₂ w₃ B₂ N₂} →
                            t ∶ B ∣ N →
               w₂ ∷ w₁ ∷ w₃ ∷ t ∶ B₂ ∣ N₂ →
    w₃ ∷ w₂ ∷ w₁ ∷ Exec-ROT ∷ t ∶ B₂ ∣ N₂

  Exec-SWAP : ∀ {t B N w₁ w₂ B₂ N₂} →
                         t ∶ B ∣ N →
                w₁ ∷ w₂ ∷ t ∶ B₂ ∣ N₂ →
    w₂ ∷ w₁ ∷ Exec-SWAP ∷ t ∶ B₂ ∣ N₂

  Exec-K : ∀ {t B N w₁ w₂ B₂ N₂} →
                      t ∶ B ∣ N →
                 w₁ ∷ t ∶ B₂ ∣ N₂ →
    w₂ ∷ w₁ ∷ Exec-K ∷ t ∶ B₂ ∣ N₂

  Exec-S : ∀ {t B N w₁ w₂ w₃ B₂ N₂} →
                           t ∶ B ∣ N →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ t ∶ B₂ ∣ N₂ →
    w₃ ∷ w₂ ∷ w₁ ∷ Exec-S ∷ t ∶ B₂ ∣ N₂

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

private
  ----------------------------------------------------------------

  eg-term : Term
  eg-term = AND ∷ true ∷ GT ∷ nat 4 ∷ nat 7 ∷ []

  eg-type : Well eg-term
  eg-type = AND (true (GT (nat (nat empty))))

  ----------------------------------------------------------------

  fix-term : Term
  fix-term = GT ∷ Exec-POP ∷ nat 7 ∷ []

  fix-type : Well fix-term
  fix-type = Exec-POP (nat empty)

  ----------------------------------------------------------------

  break-term : Term
  break-term = GT ∷ nat 4 ∷ Exec-POP ∷ nat 7 ∷ []

  break-type : ∀ N → Ill {N = N} break-term
  break-type _ (GT (Exec-POP (nat ())))
  break-type _ (GT (nat ()))

  ----------------------------------------------------------------

  swap-term : Term
  swap-term = nat 2 ∷ nat 3 ∷ Exec-SWAP ∷ nat 1 ∷ []

  swap-type : Well swap-term
  swap-type = Exec-SWAP one (nat (nat one))
    where
    one : Well (nat 1 ∷ [])
    one = nat empty

  ----------------------------------------------------------------

  good-swap-term : Term
  good-swap-term = GT ∷ NOT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  good-swap-type : Well good-swap-term
  good-swap-type = Exec-SWAP two (NOT (GT two))
    where
    two : Well (nat 2 ∷ nat 1 ∷ [])
    two = nat (nat empty)

  ----------------------------------------------------------------

  bad-swap-term : Term
  bad-swap-term = NOT ∷ GT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  bad-swap-type : ∀ B N → Ill {B = B} {N = N} bad-swap-term
  bad-swap-type .(suc (suc B)) N
    (Exec-SWAP (nat (nat empty)) (GT (NOT {.(nat 2 ∷ nat 1 ∷ [])} {B} (nat (nat ())))))
  bad-swap-type .(suc B) N
    (NOT {.(GT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ [])} {B} (GT ()))

  ----------------------------------------------------------------

  good-rot-term : Term
  good-rot-term = true ∷ AND ∷ false ∷ Exec-ROT ∷ []

  good-rot-type : Well good-rot-term
  good-rot-type = Exec-ROT empty p
    where
    p : Well (AND ∷ false ∷ true ∷ [])
    p = AND (false (true empty))

  ----------------------------------------------------------------

  bad-rot-term : Term
  bad-rot-term = AND ∷ false ∷ true ∷ Exec-ROT ∷ []

  bad-rot-type : ∀ B N → Ill {B = B} {N = N} bad-rot-term
  bad-rot-type .(suc (suc (suc B))) _ (Exec-ROT empty (false (true (AND {.[]} {B} ()))))
  bad-rot-type .(suc B) _ (AND {.(false ∷ true ∷ Exec-ROT ∷ [])} {B} (false (true ())))

  ----------------------------------------------------------------

  good-k-term : Term
  good-k-term = NOT ∷ nat 3 ∷ Exec-K ∷ []

  good-k-type : Well good-k-term
  good-k-type = Exec-K empty (nat empty)

  ----------------------------------------------------------------

  good-s-term : Term
  good-s-term = NOT ∷ AND ∷ false ∷ Exec-S ∷ true ∷ []

  good-s-type : Well good-s-term
  good-s-type = Exec-S p (AND (NOT (NOT (false p))))
    where
    p : Well (true ∷ [])
    p = true empty

  ----------------------------------------------------------------

  bad-s-term : Term
  bad-s-term = AND ∷ NOT ∷ false ∷ Exec-S ∷ true ∷ []

  bad-s-type : ∀ B N → Ill {B = B} {N = N} bad-s-term
  bad-s-type .(suc B) N (Exec-S (true empty) (NOT {.(AND ∷ AND ∷ false ∷ true ∷ [])} {B} (AND (AND (false (true ()))))))
  bad-s-type .(suc B) N (AND {.(NOT ∷ false ∷ Exec-S ∷ true ∷ [])} {B} (NOT (false ())))

  ----------------------------------------------------------------

  bad-k-term : Term
  bad-k-term = nat 3 ∷ NOT ∷ Exec-K ∷ []

  bad-k-type : ∀ B N → Ill {B = B} {N = N} bad-k-term
  bad-k-type .(suc B) N (Exec-K empty (NOT {.[]} {B} ()))
  bad-k-type .(suc B) .(suc N) (nat {.(NOT ∷ Exec-K ∷ [])} {.(suc B)} {N} (NOT {.(Exec-K ∷ [])} {B} ()))

  ----------------------------------------------------------------

  good-eq-term : Term
  good-eq-term = AND ∷ AND ∷ Exec-EQ ∷ []

  good-eq-type : Well good-eq-term
  good-eq-type = Exec-EQ empty

  ----------------------------------------------------------------

  bad-eq-term : Term
  bad-eq-term = AND ∷ Exec-EQ ∷ []

  bad-eq-type : ∀ B N → Ill {B = B} {N = N} bad-eq-term
  bad-eq-type .(suc B) N (AND {.(Exec-EQ ∷ [])} {B} ())

  ----------------------------------------------------------------

  good-dup-term : Term
  good-dup-term = NOT ∷ Exec-DUP ∷ true ∷ []

  good-dup-type : Well good-dup-term
  good-dup-type = Exec-DUP p (NOT (NOT p))
    where
    p : Well (true ∷ [])
    p = true empty

  ----------------------------------------------------------------

  bad-dup-term : Term
  bad-dup-term = NOT ∷ Exec-DUP ∷ []

  bad-dup-type : ∀ B N → Ill {B = B} {N = N} bad-dup-term
  bad-dup-type .(suc B) N (Exec-DUP empty (NOT {.(NOT ∷ [])} {B} (NOT ())))
  bad-dup-type .(suc B) N (NOT {.(Exec-DUP ∷ [])} {B} ())

  ----------------------------------------------------------------

data Typed (t : Term) : Set where
  well : ∀ {B N} → Well {B} {N} t → Typed t
  ill  : Typed t
