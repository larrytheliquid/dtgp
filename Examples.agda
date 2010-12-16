module Examples where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Vec
open import Stash
open import Check
open import Run

private
  ----------------------------------------------------------------

  eg-term : Term
  eg-term = AND ∷ true ∷ GT ∷ nat 4 ∷ nat 7 ∷ []

  eg-type : Well eg-term
  eg-type = AND (true (GT (nat (nat empty))))

  eg-check : check eg-term ≡ well eg-type
  eg-check = refl

  eg-run : run eg-type ≡ env (true ∷ []) []
  eg-run = refl

  ----------------------------------------------------------------

  fix-term : Term
  fix-term = GT ∷ Exec-POP ∷ nat 7 ∷ []

  fix-type : Well fix-term
  fix-type = Exec-POP (nat empty)

  fix-check : check fix-term ≡ well fix-type
  fix-check = refl

  fix-run : run fix-type ≡ env [] (7 ∷ [])
  fix-run = refl

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

  swap-check : check swap-term ≡ well swap-type
  swap-check = refl

  swap-run : run swap-type ≡ env [] (3 ∷ 2 ∷ 1 ∷ [])
  swap-run = refl

  ----------------------------------------------------------------

  good-swap-term : Term
  good-swap-term = GT ∷ NOT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  good-swap-type : Well good-swap-term
  good-swap-type = Exec-SWAP two (NOT (GT two))
    where
    two : Well (nat 2 ∷ nat 1 ∷ [])
    two = nat (nat empty)

  good-swap-check : check good-swap-term ≡ well good-swap-type
  good-swap-check = refl

  good-swap-run : run good-swap-type ≡ env (true ∷ []) []
  good-swap-run = refl

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

  good-rot-check : check good-rot-term ≡ well good-rot-type
  good-rot-check = refl

  good-rot-run : run good-rot-type ≡ env (false ∷ []) []
  good-rot-run = refl

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

  good-k-check : check good-k-term ≡ well good-k-type
  good-k-check = refl

  good-k-run : run good-k-type ≡ env [] (3 ∷ [])
  good-k-run = refl

  ----------------------------------------------------------------

  good-s-term : Term
  good-s-term = NOT ∷ AND ∷ false ∷ Exec-S ∷ true ∷ []

  good-s-type : Well good-s-term
  good-s-type = Exec-S p (AND (NOT (NOT (false p))))
    where
    p : Well (true ∷ [])
    p = true empty

  good-s-check : check good-s-term ≡ well good-s-type
  good-s-check = refl

  good-s-run : run good-s-type ≡ env (false ∷ []) []
  good-s-run = refl

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

  good-eq-check : check good-eq-term ≡ well good-eq-type
  good-eq-check = refl

  good-eq-run : run good-eq-type ≡ env (true ∷ []) []
  good-eq-run = refl

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

  good-dup-check : check good-dup-term ≡ well good-dup-type
  good-dup-check = refl

  good-dup-run : run good-dup-type ≡ env (true ∷ []) []
  good-dup-run = refl

  ----------------------------------------------------------------

  bad-dup-term : Term
  bad-dup-term = NOT ∷ Exec-DUP ∷ []

  bad-dup-type : ∀ B N → Ill {B = B} {N = N} bad-dup-term
  bad-dup-type .(suc B) N (Exec-DUP empty (NOT {.(NOT ∷ [])} {B} (NOT ())))
  bad-dup-type .(suc B) N (NOT {.(Exec-DUP ∷ [])} {B} ())

  ----------------------------------------------------------------
