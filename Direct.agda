module Direct where
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_∸_)
open import Data.Bool
open import Data.Vec

infixl 2 _⟶_
infixr 5 _,_
infixl 6 _∸_

_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

lem : ∀ n → n ∸ 0 ≡ n
lem zero = refl
lem (suc n) = refl

-- data Least : ℕ → Set where
--   zero : {n : ℕ} → Least n
--   suc  : {n : ℕ} (i : Least n) → Least (suc n)

-- one : Least 3
-- one = suc (suc (suc (suc zero)))

data Word : Set where
  true false Bool-POP AND NOT : Word

-- In : Word → (n : ℕ) → Least n

In : Word → ℕ
In true = 0
In false = 0
In Bool-POP = 1
In AND = 2
In NOT = 1

Out : Word → ℕ
Out true = 1
Out false = 1
Out Bool-POP = 0
Out AND = 1
Out NOT = 1

data _⟶_ : (B B' : ℕ) → Set where
  []  : 0 ⟶ 0
  _,_ : ∀ {B B'} → (w : Word) →
    B ⟶ B' →
    In w + (B ∸ Out w) ⟶
    (Out w ∸ B) + B'

private
  and,and : 3 ⟶ 1
  and,and = AND , AND , []

  not,and : 2 ⟶ 1
  not,and = NOT , AND , []

  not,not : 1 ⟶ 1
  not,not = NOT , NOT , []

  long : 0 ⟶ 1
  long = false , NOT , true , AND , []

run : {B B' : ℕ} →
  B ⟶ B' → Vec Bool B → Vec Bool B'
run [] [] = []

run (_,_ {zero} true d) xs =
  true ∷ run d []
run (_,_ {suc n} true d) xs rewrite lem n =
  run d (true ∷ xs)

run (_,_ {zero} false d) xs =
  false ∷ run d []
run (_,_ {suc n} false d) xs rewrite lem n =
  run d (false ∷ xs)

run (_,_ {zero}  Bool-POP d) (x ∷ []) =
  run d []
run (_,_ {suc n} Bool-POP d) (x ∷ xs) rewrite lem n =
  run d xs

run (_,_ {zero}  AND d) (x₁ ∷ x₂ ∷ xs) =
  x₂ ∧ x₁ ∷ run d []
run (_,_ {suc n} AND d) (x₁ ∷ x₂ ∷ xs) rewrite lem n =
  run d (x₂ ∧ x₁ ∷ xs)

run (_,_ {zero}  NOT d) (x ∷ []) =
  not x ∷ run d []
run (_,_ {suc n} NOT d) (x ∷ xs) rewrite lem n =
  run d (not x ∷ xs)



