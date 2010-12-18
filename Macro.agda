module Macro where
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Term

infixl 2 _⊢_

data _⊢_ : ∀ {m n} (E : Term m) (t : Term n) → Set where
  empty : [] ⊢ []

  Exec-DUP : ∀ {m n w} {E : Term m} {t : Term n} →
           w ∷ w ∷ E ⊢ t →
    Exec-DUP ∷ w ∷ E ⊢ t

  Exec-K : ∀ {m n w₁ w₂} {E : Term m} {t : Term n} →
                 w₁ ∷ E ⊢ t →
    Exec-K ∷ w₁ ∷ w₂ ∷ E ⊢ t

  true : ∀ {m n} {E : Term m} {t : Term n} →
           E ⊢ t →
    true ∷ E ⊢ t ∷ʳ true

  false : ∀ {m n} {E : Term m} {t : Term n} →
            E ⊢ t →
    false ∷ E ⊢ t ∷ʳ false

  NOT : ∀ {m n} {E : Term m} {t : Term n} →
          E ⊢ t →
    NOT ∷ E ⊢ t ∷ʳ NOT

  nat : ∀ {m n v} {E : Term m} {t : Term n} →
           E ⊢ t →
    nat  v ∷ E ⊢ t ∷ʳ nat v

-- expand : ∀ {m n} {t : Term n} (E : Term m) → E ⊢ t
-- expand [] = {!!}
-- expand (x ∷ xs) = {!!}

-- expand [] = well empty
-- expand (Exec-POP ∷ w ∷ t) = check-2 (expand t) w Exec-POP
-- expand (Exec-DUP ∷ w ∷ t) = check-2 (expand t) w Exec-DUP
-- expand (Exec-EQ ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-EQ
-- expand (Exec-K ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-K
-- expand (Exec-SWAP ∷ w₁ ∷ w₂ ∷ t) = check-3 (check t) w₂ w₁ Exec-SWAP
-- expand (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) = check-4 (check t) w₃ w₂ w₁ Exec-ROT
-- expand (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ t) = check-4 (check t) w₃ w₂ w₁ Exec-S
-- expand (Exec-STACKDEPTH ∷ t) with expand t
-- ... | well p = well (Exec-STACKDEPTH [] p)
-- ... | ill = ill
-- expand (w ∷ t) = ?
