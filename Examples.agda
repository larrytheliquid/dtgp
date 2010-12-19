module Examples where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Check

private
  ----------------------------------------------------------------

  eg-term : Term 5
  eg-term = nat 7 ∷ nat 4 ∷ GT ∷ true ∷ AND ∷ []

  eg-type : Well eg-term
  eg-type = nat (nat (GT (true (AND empty))))

  eg-check : check eg-term ≡ well eg-type
  eg-check = refl

  -- eg-run : run eg-type ≡ env (true ∷ []) []
  -- eg-run = refl

  ----------------------------------------------------------------

  fix-term : Term 3
  fix-term = nat 7 ∷ Exec-POP ∷ GT ∷ []

  fix-type : Well fix-term
  fix-type = nat (Exec-POP empty)

  fix-check : check fix-term ≡ well fix-type
  fix-check = refl

  -- fix-run : run fix-type ≡ env [] (7 ∷ [])
  -- fix-run = refl

  ----------------------------------------------------------------

  break-term : Term 4
  break-term = nat 7 ∷ Exec-POP ∷ nat 4 ∷ GT ∷ []

  break-type : Ill break-term
  break-type (nat (Exec-POP ()))

  ----------------------------------------------------------------

  swap-term : Term 4
  swap-term = nat 1 ∷ Exec-SWAP ∷ nat 3 ∷ nat 2 ∷ []

  swap-type : Well swap-term
  swap-type = nat (Exec-SWAP (nat (nat empty)))

  swap-check : check swap-term ≡ well swap-type
  swap-check = refl

  -- swap-run : run swap-type ≡ env [] (3 ∷ 2 ∷ 1 ∷ [])
  -- swap-run = refl

  ----------------------------------------------------------------

  good-swap-term : Term 5
  good-swap-term = nat 1 ∷ nat 2 ∷ Exec-SWAP ∷ NOT ∷ GT ∷ []

  good-swap-type : Well good-swap-term
  good-swap-type = nat (nat (Exec-SWAP (GT (NOT empty))))

  good-swap-check : check good-swap-term ≡ well good-swap-type
  good-swap-check = refl

  -- good-swap-run : run good-swap-type ≡ env (true ∷ []) []
  -- good-swap-run = refl

  ----------------------------------------------------------------

  bad-swap-term : Term 5
  bad-swap-term = nat 1 ∷ nat 2 ∷ Exec-SWAP ∷ GT ∷ NOT ∷ []

  bad-swap-type : Ill bad-swap-term
  bad-swap-type (nat (nat (Exec-SWAP ())))

  ----------------------------------------------------------------

  good-rot-term : Term 4
  good-rot-term = Exec-ROT ∷ false ∷ AND ∷ true ∷ []

  good-rot-type : Well good-rot-term
  good-rot-type = Exec-ROT (true (false (AND empty)))

  good-rot-check : check good-rot-term ≡ well good-rot-type
  good-rot-check = refl

  -- good-rot-run : run good-rot-type ≡ env (false ∷ []) []
  -- good-rot-run = refl

  ----------------------------------------------------------------

  bad-rot-term : Term 4
  bad-rot-term = Exec-ROT ∷ true ∷ false ∷ AND ∷ []

  bad-rot-type : Ill bad-rot-term
  bad-rot-type (Exec-ROT ())

  ----------------------------------------------------------------

  good-k-term : Term 3
  good-k-term = Exec-K ∷ nat 3 ∷ NOT ∷ []

  good-k-type : Well good-k-term
  good-k-type = Exec-K (nat empty)

  good-k-check : check good-k-term ≡ well good-k-type
  good-k-check = refl

  -- good-k-run : run good-k-type ≡ env [] (3 ∷ [])
  -- good-k-run = refl

  ----------------------------------------------------------------

  bad-k-term : Term 3
  bad-k-term = Exec-K ∷ NOT ∷ nat 3 ∷ []

  bad-k-type : Ill bad-k-term
  bad-k-type (Exec-K ())

  ----------------------------------------------------------------

  good-s-term : Term 5
  good-s-term = true ∷ Exec-S ∷ AND ∷ NOT ∷ false ∷ []

  good-s-type : Well good-s-term
  good-s-type = true (Exec-S (NOT (false (false (AND empty)))))

  -- good-s-check : check good-s-term ≡ well good-s-type
  -- good-s-check = refl

  -- good-s-run : run good-s-type ≡ env (false ∷ []) []
  -- good-s-run = refl

  ----------------------------------------------------------------

  bad-s-term : Term 5
  bad-s-term = true ∷ Exec-S ∷ false ∷ NOT ∷ AND ∷ []

  bad-s-type : Ill bad-s-term
  bad-s-type (true (Exec-S (NOT ())))

  ----------------------------------------------------------------

  good-eq-term : Term 3
  good-eq-term = Exec-EQ ∷ AND ∷ AND ∷ []

  good-eq-type : Well good-eq-term
  good-eq-type = Exec-EQ empty

  good-eq-check : check good-eq-term ≡ well good-eq-type
  good-eq-check = refl

  -- good-eq-run : run good-eq-type ≡ env (true ∷ []) []
  -- good-eq-run = refl

  ----------------------------------------------------------------

  bad-eq-term : Term 2
  bad-eq-term = Exec-EQ ∷ AND ∷ []

  bad-eq-type : Ill bad-eq-term
  bad-eq-type ()

  ----------------------------------------------------------------

  good-dup-term : Term 3
  good-dup-term = true ∷ Exec-DUP ∷ NOT ∷ []

  good-dup-type : Well good-dup-term
  good-dup-type = true (Exec-DUP (NOT (NOT empty)))

  -- good-dup-check : check good-dup-term ≡ well good-dup-type
  -- good-dup-check = refl

  -- good-dup-run : run good-dup-type ≡ env (true ∷ []) []
  -- good-dup-run = refl

  ----------------------------------------------------------------

  bad-dup-term : Term 2
  bad-dup-term = Exec-DUP ∷ NOT ∷ []

  bad-dup-type : Ill bad-dup-term
  bad-dup-type (Exec-DUP ())

  ----------------------------------------------------------------

  good-depth-term : Term 5
  good-depth-term = true ∷ Exec-STACKDEPTH ∷ NOT ∷ NOT ∷ NOT ∷ []

  good-depth-type : Well good-depth-term
  good-depth-type = true (Exec-STACKDEPTH (NOT (NOT (NOT empty))))

  good-depth-check : check good-depth-term ≡ well good-depth-type
  good-depth-check = refl

  -- good-depth-run : run good-depth-type ≡ env (false ∷ []) (3 ∷ [])
  -- good-depth-run = refl

  ----------------------------------------------------------------

  meta-term : Term 4
  meta-term = Exec-K ∷ Exec-DUP ∷ Exec-K ∷ true ∷ []

  meta-type : Well meta-term
  meta-type = Exec-K (Exec-DUP (true (true empty)))

  -- meta-check : check meta-term ≡ well meta-type
  -- meta-check = refl
