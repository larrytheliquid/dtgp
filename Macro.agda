module Macro where
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Maybe
open import Term

infixl 2 _⊢_

data _⊢_ : ∀ {m n} (E : Term m) (t : Term n) → Set where
  empty : [] ⊢ []

  Exec-POP : ∀ {m n w} {E : Term m} {t : Term n} →
                   E ⊢ t →
    Exec-POP ∷ w ∷ E ⊢ t

  Exec-DUP : ∀ {m n w} {E : Term m} {t : Term n} →
           w ∷ w ∷ E ⊢ t →
    Exec-DUP ∷ w ∷ E ⊢ t

  Exec-EQ : ∀ {m n w₁ w₂} {E : Term m} {t : Term n} →
                       E ⊢ t →
    Exec-EQ ∷ w₁ ∷ w₂ ∷ E ⊢ t

  Exec-K : ∀ {m n w₁ w₂} {E : Term m} {t : Term n} →
                 w₁ ∷ E ⊢ t →
    Exec-K ∷ w₁ ∷ w₂ ∷ E ⊢ t

  Exec-SWAP : ∀ {m n w₁ w₂} {E : Term m} {t : Term n} →
                w₂ ∷ w₁ ∷ E ⊢ t →
    Exec-SWAP ∷ w₁ ∷ w₂ ∷ E ⊢ t

  Exec-ROT : ∀ {m n w₁ w₂ w₃} {E : Term m} {t : Term n} →
               w₃ ∷ w₁ ∷ w₂ ∷ E ⊢ t →
    Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ E ⊢ t

  Exec-S : ∀ {m n w₁ w₂ w₃} {E : Term m} {t : Term n} →
        w₂ ∷ w₃ ∷ w₃ ∷ w₁ ∷ E ⊢ t →
    Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ E ⊢ t

  Exec-STACKDEPTH : ∀ {m n} {E : Term m} {t : Term n} →
                      E ⊢ t →
    Exec-STACKDEPTH ∷ E ⊢ t

  true : ∀ {m n} {E : Term m} {t : Term n} →
           E ⊢ t →
    true ∷ E ⊢ t ∷ʳ true

  false : ∀ {m n} {E : Term m} {t : Term n} →
            E ⊢ t →
    false ∷ E ⊢ t ∷ʳ false

  Bool-POP : ∀ {m n} {E : Term m} {t : Term n} →
               E ⊢ t →
    Bool-POP ∷ E ⊢ t ∷ʳ Bool-POP

  AND : ∀ {m n} {E : Term m} {t : Term n} →
          E ⊢ t →
    AND ∷ E ⊢ t ∷ʳ AND

  NOT : ∀ {m n} {E : Term m} {t : Term n} →
          E ⊢ t →
    NOT ∷ E ⊢ t ∷ʳ NOT

  nat : ∀ {m n v} {E : Term m} {t : Term n} →
            E ⊢ t →
    nat v ∷ E ⊢ t ∷ʳ nat v

  Nat-POP : ∀ {m n} {E : Term m} {t : Term n} →
              E ⊢ t →
    Nat-POP ∷ E ⊢ t ∷ʳ Nat-POP

  ADD : ∀ {m n} {E : Term m} {t : Term n} →
          E ⊢ t →
    ADD ∷ E ⊢ t ∷ʳ ADD

  LT : ∀ {m n} {E : Term m} {t : Term n} →
         E ⊢ t →
    LT ∷ E ⊢ t ∷ʳ LT

  GT : ∀ {m n} {E : Term m} {t : Term n} →
         E ⊢ t →
    GT ∷ E ⊢ t ∷ʳ GT

data Expanded {m} (E : Term m) : Set where
  well : ∀ {n} {t : Term n} → E ⊢ t → Expanded E
  ill  : Expanded E

expand' : ∀ {m} {E : Term m} → (w : Word) → Expanded E → Expanded (w ∷ E)
expand' true (well p) = well (true p)
expand' false (well p) = well (false p)
expand' Bool-POP (well p) = well (Bool-POP p)
expand' AND (well p) = well (AND p)
expand' NOT (well p) = well (NOT p)
expand' Nat-POP (well p) = well (Nat-POP p)
expand' ADD (well p) = well (ADD p)
expand' LT (well p) = well (LT p)
expand' GT (well p) = well (GT p)
expand' (nat _) (well p) = well (nat p)
expand' _ _ = ill

expand : ∀ {m} (E : Term m) → Expanded E
expand [] = well empty
expand (Exec-POP ∷ w ∷ E) with expand E
... | well p = well (Exec-POP p)
... | ill = ill
-- TODO: analyze
expand (Exec-DUP ∷ w ∷ E) with expand (w ∷ E)
... | ih with expand' w ih
... | well p = well (Exec-DUP p)
... | ill = ill
expand (Exec-EQ ∷ w₁ ∷ w₂ ∷ E) with expand E
... | well p = well (Exec-EQ p)
... | ill = ill
expand (Exec-K ∷ w₁ ∷ w₂ ∷ E) with expand (w₁ ∷ E)
... | well p = well (Exec-K p)
... | ill = ill
expand (Exec-SWAP ∷ w₁ ∷ w₂ ∷ E) with expand (w₂ ∷ w₁ ∷ E)
... | well p = well (Exec-SWAP p)
... | ill = ill
expand (Exec-ROT ∷ w₁ ∷ w₂ ∷ w₃ ∷ E) with expand (w₃ ∷ w₁ ∷ w₂ ∷ E)
... | well p = well (Exec-ROT p)
... | ill = ill
-- TODO: analyze
expand (Exec-S ∷ w₁ ∷ w₂ ∷ w₃ ∷ E) with expand (w₃ ∷ w₃ ∷ w₁ ∷ E)
... | ih with expand' w₂ ih
... | well p = well (Exec-S p)
... | ill = ill
expand (Exec-STACKDEPTH ∷ E) with expand E
... | well p = well (Exec-STACKDEPTH p)
... | ill = ill
expand (w ∷ E) = expand' w (expand E)

