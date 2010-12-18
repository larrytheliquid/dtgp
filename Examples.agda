module Examples where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Term
open import Macro
open import Expanded

private
  ----------------------------------------------------------------

  eg-term : Term 5
  eg-term = AND ∷ true ∷ GT ∷ nat 4 ∷ nat 7 ∷ []
  -- eg-term = nat 7 ∷ nat 4 ∷ GT ∷ true ∷ AND ∷ []

  eg-type : eg-term ∶ 1 ∣ 0
  eg-type = AND (true (GT (nat (nat empty))))
  -- eg-type = nat (nat (GT (true (AND {!!}))))

  -- eg-check : ona eg-term ≡ well eg-type
  -- eg-check = refl

  -- eg-run : run eg-type ≡ env (true ∷ []) []
  -- eg-run = refl

  -- ----------------------------------------------------------------

  -- fix-term : Term 3
  -- fix-term = GT ∷ Exec-POP ∷ nat 7 ∷ []

  -- fix-type : Well fix-term
  -- fix-type = Exec-POP (nat empty)

  -- fix-check : check fix-term ≡ well fix-type
  -- fix-check = refl

  -- fix-run : run fix-type ≡ env [] (7 ∷ [])
  -- fix-run = refl

  -- ----------------------------------------------------------------

  -- -- break-term : Term 4
  -- -- break-term = GT ∷ nat 4 ∷ Exec-POP ∷ nat 7 ∷ []

  -- -- break-type : ∀ N → Ill {N = N} break-term
  -- -- break-type _ (GT (Exec-POP (nat ())))
  -- -- break-type _ (GT (nat ()))

  -- ----------------------------------------------------------------

  -- swap-term : Term 4
  -- swap-term = nat 2 ∷ nat 3 ∷ Exec-SWAP ∷ nat 1 ∷ []

  -- swap-type : Well swap-term
  -- swap-type = Exec-SWAP (nat (nat (nat empty)))

  -- swap-check : check swap-term ≡ well swap-type
  -- swap-check = refl

  -- swap-run : run swap-type ≡ env [] (3 ∷ 2 ∷ 1 ∷ [])
  -- swap-run = refl

  -- ----------------------------------------------------------------

  -- good-swap-term : Term 5
  -- good-swap-term = GT ∷ NOT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  -- good-swap-type : Well good-swap-term
  -- good-swap-type = Exec-SWAP (NOT (GT (nat (nat empty))))

  -- good-swap-check : check good-swap-term ≡ well good-swap-type
  -- good-swap-check = refl

  -- good-swap-run : run good-swap-type ≡ env (true ∷ []) []
  -- good-swap-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-swap-term : Term 5
  -- -- bad-swap-term = NOT ∷ GT ∷ Exec-SWAP ∷ nat 2 ∷ nat 1 ∷ []

  -- -- bad-swap-type : ∀ B N → Ill {B = B} {N = N} bad-swap-term
  -- -- bad-swap-type .(suc (suc B)) N (Exec-SWAP (GT (NOT {.2} {B} (nat (nat ())))))
  -- -- bad-swap-type .(suc B) N (NOT {.4} {B} (GT ()))

  -- ----------------------------------------------------------------

  -- good-rot-term : Term 4
  -- good-rot-term = true ∷ AND ∷ false ∷ Exec-ROT ∷ []

  -- good-rot-type : Well good-rot-term
  -- good-rot-type = Exec-ROT (AND (false (true empty)))

  -- good-rot-check : check good-rot-term ≡ well good-rot-type
  -- good-rot-check = refl

  -- good-rot-run : run good-rot-type ≡ env (false ∷ []) []
  -- good-rot-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-rot-term : Term 4
  -- -- bad-rot-term = AND ∷ false ∷ true ∷ Exec-ROT ∷ []

  -- -- bad-rot-type : ∀ B N → Ill {B = B} {N = N} bad-rot-term
  -- -- bad-rot-type .(suc (suc (suc B))) N (Exec-ROT (false (true (AND {.0} {B} ()))))
  -- -- bad-rot-type .(suc B) N (AND {.3} {B} (false (true ())))

  -- ----------------------------------------------------------------

  -- good-k-term : Term 3
  -- good-k-term = NOT ∷ nat 3 ∷ Exec-K ∷ []

  -- good-k-type : Well good-k-term
  -- good-k-type = Exec-K (nat empty)

  -- good-k-check : check good-k-term ≡ well good-k-type
  -- good-k-check = refl

  -- good-k-run : run good-k-type ≡ env [] (3 ∷ [])
  -- good-k-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-k-term : Term 3
  -- -- bad-k-term = nat 3 ∷ NOT ∷ Exec-K ∷ []

  -- -- bad-k-type : ∀ B N → Ill {B = B} {N = N} bad-k-term
  -- -- bad-k-type .(suc B) N (Exec-K (NOT {.0} {B} ()))
  -- -- bad-k-type .(suc B) .(suc N) (nat {.2} {.(suc B)} {N} (NOT {.1} {B} ()))

  -- ----------------------------------------------------------------

  -- good-s-term : Term 5
  -- good-s-term = NOT ∷ AND ∷ false ∷ Exec-S ∷ true ∷ []

  -- good-s-type : Well good-s-term
  -- good-s-type = Exec-S (AND (NOT (NOT (false (true empty)))))

  -- good-s-check : check good-s-term ≡ well good-s-type
  -- good-s-check = refl

  -- good-s-run : run good-s-type ≡ env (false ∷ []) []
  -- good-s-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-s-term : Term 5
  -- -- bad-s-term = AND ∷ NOT ∷ false ∷ Exec-S ∷ true ∷ []

  -- -- bad-s-type : ∀ B N → Ill {B = B} {N = N} bad-s-term
  -- -- bad-s-type .(suc B) N (Exec-S (NOT {.4} {B} (AND (AND (false (true ()))))))
  -- -- bad-s-type .(suc B) N (AND {.4} {B} (NOT (false ())))

  -- ----------------------------------------------------------------

  -- good-eq-term : Term 3
  -- good-eq-term = AND ∷ AND ∷ Exec-EQ ∷ []

  -- good-eq-type : Well good-eq-term
  -- good-eq-type = Exec-EQ empty

  -- good-eq-check : check good-eq-term ≡ well good-eq-type
  -- good-eq-check = refl

  -- good-eq-run : run good-eq-type ≡ env (true ∷ []) []
  -- good-eq-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-eq-term : Term 2
  -- -- bad-eq-term = AND ∷ Exec-EQ ∷ []

  -- -- bad-eq-type : ∀ B N → Ill {B = B} {N = N} bad-eq-term
  -- -- bad-eq-type .(suc B) N (AND {.1} {B} ())

  -- ----------------------------------------------------------------

  -- good-dup-term : Term 3
  -- good-dup-term = NOT ∷ Exec-DUP ∷ true ∷ []

  -- good-dup-type : Well good-dup-term
  -- good-dup-type = Exec-DUP (NOT (NOT (true empty)))

  -- good-dup-check : check good-dup-term ≡ well good-dup-type
  -- good-dup-check = refl

  -- good-dup-run : run good-dup-type ≡ env (true ∷ []) []
  -- good-dup-run = refl

  -- ----------------------------------------------------------------

  -- -- bad-dup-term : Term 2
  -- -- bad-dup-term = NOT ∷ Exec-DUP ∷ []

  -- -- bad-dup-type : ∀ B N → Ill {B = B} {N = N} bad-dup-term
  -- -- bad-dup-type .(suc B) N (Exec-DUP (NOT {.1} {B} (NOT ())))
  -- -- bad-dup-type .(suc B) N (NOT {.1} {B} ())

  -- ----------------------------------------------------------------

  -- good-depth-term : Term 5
  -- good-depth-term = NOT ∷ NOT ∷ NOT ∷ Exec-STACKDEPTH ∷ true ∷ []

  -- good-depth-type : Well good-depth-term
  -- good-depth-type = Exec-STACKDEPTH (NOT ∷ NOT ∷ NOT ∷ [])
  --   (NOT (NOT (NOT (true empty))))

  -- -- good-depth-run : run good-depth-type ≡ env (false ∷ []) (3 ∷ [])
  -- -- good-depth-run = refl

  ----------------------------------------------------------------

  my-macro : Term 4
  my-macro = Exec-K ∷ Exec-DUP ∷ Exec-K ∷ true ∷ []

  my-expanded : Term 2
  my-expanded = true ∷ true ∷ []

  my-expansion : my-macro ⊢ my-expanded
  my-expansion = Exec-K (Exec-DUP (true (true empty)))

  my-expand : expand my-macro ≡ well my-expansion
  my-expand = refl

  my-type : my-expanded ∶ 2 ∣ 0
  my-type = true (true empty)

  my-check : check my-expanded ≡ well my-type
  my-check = refl
