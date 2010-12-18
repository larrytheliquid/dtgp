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

  Exec-DUP : ∀ {n w} {t : Term n} →
           w ∷ w ∷ t ⊢ t →
    Exec-DUP ∷ w ∷ t ⊢ t

  Exec-K : ∀ {n w₁ w₂} {t : Term n} →
                 w₁ ∷ t ⊢ t →
    Exec-K ∷ w₁ ∷ w₂ ∷ t ⊢ t

  true : ∀ {n} {t : Term n} →
           t ⊢ t →
    true ∷ t ⊢ t ∷ʳ true

  false : ∀ {n} {t : Term n} →
            t ⊢ t →
    false ∷ t ⊢ t ∷ʳ false

  Bool-POP : ∀ {n} {t : Term n} →
               t ⊢ t →
    Bool-POP ∷ t ⊢ t ∷ʳ Bool-POP

  AND : ∀ {n} {t : Term n} →
          t ⊢ t →
    AND ∷ t ⊢ t ∷ʳ AND

  NOT : ∀ {n} {t : Term n} →
          t ⊢ t →
    NOT ∷ t ⊢ t ∷ʳ NOT

  nat : ∀ {n v} {t : Term n} →
            t ⊢ t →
    nat v ∷ t ⊢ t ∷ʳ nat v

  Nat-POP : ∀ {n} {t : Term n} →
              t ⊢ t →
    Nat-POP ∷ t ⊢ t ∷ʳ Nat-POP

  ADD : ∀ {n} {t : Term n} →
          t ⊢ t →
    ADD ∷ t ⊢ t ∷ʳ ADD

  LT : ∀ {n} {t : Term n} →
         t ⊢ t →
    LT ∷ t ⊢ t ∷ʳ LT

  GT : ∀ {n} {t : Term n} →
         t ⊢ t →
    GT ∷ t ⊢ t ∷ʳ GT

data Expanded {m} (E : Term m) : Set where
  well : ∀ {n} {t : Term n} → E ⊢ t → Expanded E
  ill  : Expanded E

-- expand-1 : ∀ {m} {E : Term m} → Expanded E → (w : Word) → Expanded (w ∷ E)
-- expand-1 (well p) true = well (true {!!})
-- -- expand-1 (well p) false = well (false p)
-- -- expand-1 (well p) Bool-POP = well (Bool-POP p)
-- -- expand-1 (well p) AND = well (AND p)
-- -- expand-1 (well p) NOT = well (NOT p)
-- -- expand-1 (well p) Nat-POP = well (Nat-POP p)
-- -- expand-1 (well p) ADD = well (ADD p)
-- -- expand-1 (well p) LT = well (LT p)
-- -- expand-1 (well p) GT = well (GT p)
-- -- expand-1 (well p) (nat _) = well (nat p)
-- expand-1 _ _ = ill

-- expand-2' : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
-- expand-2' (well p) Exec-POP w = well (Exec-POP p)
-- expand-2' p w₁ w₂ = expand-1 (expand-1 p w₁) w₂

-- expand-2 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ : Word) → Typed (w₂ ∷ w₁ ∷ t)
-- expand-2 (well p₁) Exec-DUP w with expand-2' (well p₁) w w
-- ... | well p₂ = well (Exec-DUP p₂)
-- ... | ill = ill
-- expand-2 p w₁ w₂ = expand-2' p w₁ w₂

-- expand-3 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ : Word) → Typed (w₃ ∷ w₂ ∷ w₁ ∷ t)
-- expand-3 (well p) Exec-EQ w₁ w₂ = well (Exec-EQ p)
-- expand-3 (well p₁) Exec-SWAP w₁ w₂ with expand-2 (well p₁) w₂ w₁
-- ... | well p₂ = well (Exec-SWAP p₂)
-- ... | ill = ill
-- expand-3 (well p₁) Exec-K w₁ w₂ with expand-1 (well p₁) w₁
-- ... | well p₂ = well (Exec-K p₂)
-- ... | ill = ill
-- expand-3 p w₁ w₂ w₃ = expand-1 (expand-2 p w₁ w₂) w₃

-- expand-4' : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ w₄ : Word) → Typed (w₄ ∷ w₃ ∷ w₂ ∷ w₁ ∷ t)
-- expand-4' (well p₁) Exec-ROT w₁ w₂ w₃ with expand-3 (well p₁) w₃ w₁ w₂
-- ... | well p₂ = well (Exec-ROT p₂)
-- ... | ill = ill
-- expand-4' p w₁ w₂ w₃ w₄ = expand-1 (expand-3 p w₁ w₂ w₃) w₄

-- expand-4 : ∀ {n} {t : Term n} → Typed t → (w₁ w₂ w₃ w₄ : Word) → Typed (w₄ ∷ w₃ ∷ w₂ ∷ w₁ ∷ t)
-- expand-4 (well p₁) Exec-S w₁ w₂ w₃ with expand-4' (well p₁) w₁ w₃ w₃ w₂
-- ... | well p₂ = well (Exec-S p₂)
-- ... | ill = ill
-- expand-4 p w₁ w₂ w₃ w₄ = expand-4' p w₁ w₂ w₃ w₄

-- expand : ∀ {m} (E : Term m) → Expanded E
-- expand [] = well empty
-- expand (Exec-POP ∷ t) = ill -- TODO
-- expand (Exec-DUP ∷ w ∷ t) = {!!}
-- expand (Exec-EQ ∷ t) = ill -- TODO
-- expand (Exec-K ∷ w₁ ∷ w₂ ∷ t) = {!!}
-- expand (Exec-SWAP ∷ t) = ill -- TODO
-- expand (Exec-ROT ∷ t) = ill -- TODO
-- expand (Exec-S ∷ t) = ill -- TODO
-- expand (Exec-STACKDEPTH ∷ t) = ill -- TODO
-- expand (true ∷ t) = {!!}
-- expand (false ∷ t) = {!!}
-- expand (Bool-POP ∷ t) = {!!}
-- expand (AND ∷ t) = {!!}
-- expand (NOT ∷ t) = {!!}
-- expand (Nat-POP ∷ t) = {!!}
-- expand (ADD ∷ t) = {!!}
-- expand (LT ∷ t) = {!!}
-- expand (GT ∷ t) = {!!}
-- expand (nat v ∷ t) = {!!}
-- expand (_ ∷ _) = ill

