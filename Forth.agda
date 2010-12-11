module Forth where
open import Data.Nat
open import Data.Bool
open import Data.List

infixr 2 _∣_∣_∣_⊢_

data Word : Set where
  Exec-POP true false Bool-POP AND NOT Nat-POP ADD LT GT : Word
  nat : ℕ → Word

Term : Set
Term = List Word

data _∣_∣_∣_⊢_ : (Executing : Bool) (Exec : Term) (Bool Nat : ℕ) (t : Term) → Set where
  [] : false ∣ [] ∣ 0 ∣ 0 ⊢ []

  push : ∀ {B N t w} →
    false ∣ t ∣ B ∣ N ⊢ t →
    false ∣ w ∷ t ∣ B ∣ N ⊢ w ∷ t

  Exec-POP : ∀ {b w E B N t} →
    b ∣ Exec-POP ∷ w ∷ E ∣ B ∣ N ⊢ t →
    true ∣ E ∣ B ∣ N ⊢ t

  true : ∀ {b E B N t} →
    b ∣ true ∷ E ∣ B ∣ N ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

  false : ∀ {b E B N t} →
    b ∣ false ∷ E ∣ B ∣ N ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

  Bool-POP : ∀ {b E B N t} →
    b ∣ Bool-POP ∷ E ∣ suc B ∣ N ⊢ t →
    true ∣ E ∣ B ∣ N ⊢ t

  AND : ∀ {b E B N t} →
    b ∣ AND ∷ E ∣ suc (suc B) ∣ N ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

  NOT : ∀ {b E B N t} →
    b ∣ NOT ∷ E ∣ suc B ∣ N ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

  nat : ∀ {b E B N n t} →
    b ∣ (nat n) ∷ E ∣ B ∣ N ⊢ t →
    true ∣ E ∣ B ∣ suc N ⊢ t

  Nat-POP : ∀ {b E B N t} →
    b ∣ Nat-POP ∷ E ∣ B ∣ suc N ⊢ t →
    true ∣ E ∣ B ∣ N ⊢ t

  ADD : ∀ {b E B N t} →
    b ∣ ADD ∷ E ∣ B ∣ suc (suc N) ⊢ t →
    true ∣ E ∣ B ∣ suc N ⊢ t

  LT : ∀ {b E B N t} →
    b ∣ LT ∷ E ∣ B ∣ suc (suc N) ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

  GT : ∀ {b E B N t} →
    b ∣ GT ∷ E ∣ B ∣ suc (suc N) ⊢ t →
    true ∣ E ∣ suc B ∣ N ⊢ t

WT : {B N : ℕ} → Term → Set
WT {B} {N} t = true ∣ [] ∣ B ∣ N ⊢ t

eg-Term : Term
eg-Term = nat 3 ∷ nat 4 ∷ GT ∷ true ∷ AND ∷ []

eg-push : false ∣ eg-Term ∣ 0 ∣ 0 ⊢ eg-Term
eg-push = push (push (push (push (push []))))

eg-exec : WT eg-Term
eg-exec = AND (true (GT (nat (nat eg-push))))

pop-Term : Term
pop-Term = nat 3 ∷ Exec-POP ∷ GT ∷ []

pop-push : false ∣ pop-Term ∣ 0 ∣ 0 ⊢ pop-Term
pop-push = push (push (push []))

pop-exec : WT pop-Term
pop-exec = Exec-POP (nat pop-push)

erase : ∀ {b E B N t} → b ∣ E ∣ B ∣ N ⊢ t → Term
erase [] = []
erase (push d) = erase d
erase (Exec-POP {w = w} d) = Exec-POP ∷ w ∷ erase d
erase (true d) = true ∷ erase d
erase (false d) = false ∷ erase d
erase (Bool-POP d) = Bool-POP ∷ erase d
erase (AND d) = AND ∷ erase d
erase (NOT d) = NOT ∷ erase d
erase (nat {n = n} d) = nat n ∷ erase d
erase (Nat-POP d) = Nat-POP ∷ erase d
erase (ADD d) = ADD ∷ erase d
erase (LT d) = LT ∷ erase d
erase (GT d) = GT ∷ erase d
