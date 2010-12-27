module Take2 where
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_∸_)
open import Data.Bool
open import Data.Vec

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

lem : ∀ n → n ∸ 0 ≡ n
lem zero = refl
lem (suc n) = refl

lem-in : ∀ n → n + 0 ≡ n
lem-in zero = refl
lem-in (suc n) with lem-in n
... | p rewrite p = refl

lem-out : ∀ n → (n ∸ 0) + 0 ≡ n
lem-out zero = refl
lem-out (suc n) with lem-out n
... | p rewrite p | lem-in n = refl

lem-min : ∀ n → (n ∸ 0) ≡ n
lem-min zero = refl
lem-min (suc n) = refl

_at-least_ : ℕ → ℕ → ℕ
at at-least least = (least ∸ at) + at

data Word : Set where
  true false DEPTH POP NOT AND : Word

In : ℕ → Word → ℕ
In B true = B
In B false = B
In B DEPTH = B
In B POP = B at-least 1
In B NOT = B at-least 1
In B AND = B at-least 2

Out : ℕ → Word → ℕ
Out B true = B at-least 1
Out B false = B at-least 1
Out B DEPTH = B at-least 1
Out B POP = B
Out B NOT = B at-least 1
Out B AND = B at-least 1

infixl 2 _⊢_⟶_
infixr 5 _,_
data _⊢_⟶_ (Bot : ℕ) : (B B' : ℕ) → Set where
  []  : Bot ⊢ Bot ⟶ Bot
  _,_ : ∀ {B B'} → (w : Word) →
    Bot ⊢ B ⟶ B' →
    Bot ⊢ In B w + (B ∸ Out B' w) ⟶
    (Out B' w ∸ B') + B'

   -- Bot ⊢ In B w + (B ∸ Out B' w) ⟶ 
   --  (Out B' w ∸ B) + B'
 
private
  and : 0 ⊢ 2 ⟶ 1
  and = AND , []

  and,and : 0 ⊢ 3 ⟶ 1
  and,and = AND , AND , []

  not,and : 0 ⊢ 3 ⟶ 1
  not,and = NOT , AND , []

  not' : 0 ⊢ 1 ⟶ 1
  not' = NOT , []

  not,not : 0 ⊢ 1 ⟶ 1
  not,not = NOT , NOT , []

  false,not : 0 ⊢ 0 ⟶ 1
  false,not = false , []

  -- long : 0 ⊢ 0 ⟶ 1
  -- -- long = false , NOT , true , AND , []
  -- long = AND , true , NOT , false , []

-- run : {B B' : ℕ} →
--   0 ⊢ B ⟶ B' → Vec Bool B → Vec Bool B'
-- run [] [] = []

-- run (_,_ {zero} true d) xs =
--   true ∷ run d []
-- run (_,_ {suc n} true d) xs rewrite lem n =
--   run d (true ∷ xs)

-- run (_,_ {zero} false d) xs =
--   false ∷ run d []
-- run (_,_ {suc n} false d) xs rewrite lem n =
--   run d (false ∷ xs)

-- run (_,_ {zero} DEPTH d) xs =
--   true ∷ run d []
-- run (_,_ {suc n} DEPTH d) xs rewrite lem n =
--   run d (false ∷ xs)

-- run (_,_ {zero}  POP d) (x ∷ []) =
--   run d []
-- run (_,_ {suc n} POP d) (x ∷ xs) rewrite lem n =
--   run d xs

-- run (_,_ {zero}  AND d) (x₁ ∷ x₂ ∷ xs) =
--   x₂ ∧ x₁ ∷ run d []
-- run (_,_ {suc n} AND d) (x₁ ∷ x₂ ∷ xs) rewrite lem n =
--   run d (x₂ ∧ x₁ ∷ xs)

-- run (_,_ {zero}  NOT d) (x ∷ []) =
--   not x ∷ run d []
-- run (_,_ {suc n} NOT d) (x ∷ xs) rewrite lem n =
--   run d (not x ∷ xs)
