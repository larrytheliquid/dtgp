module Take2 where
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_∸_)
open import Data.Bool
open import Data.Vec

infixl 2 _⊢_⟶_
infixr 5 _,_
infixl 6 _∸_

_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

lem : ∀ n → n ∸ 0 ≡ n
lem zero = refl
lem (suc n) = refl

data Word (B : ℕ) : ℕ → ℕ → Set where
  true  : Word B      B  (1 + B)
  false : Word B      B  (1 + B)
  POP   : Word B (1 + B)      B
  NOT   : Word B (1 + B) (1 + B)
  AND   : Word B (2 + B) (1 + B)

data _⊢_⟶_ (Bot : ℕ) : (B B' : ℕ) → Set where
  []  : Bot ⊢ Bot ⟶ Bot
  _,_ : ∀ {B B' In Out} → (w : Word Bot In Out) →
    Bot ⊢ B ⟶ B' →
    Bot ⊢ In + (B ∸ Out) ⟶ (Out ∸ B) + B'

private
  and : 0 ⊢ 2 ⟶ 1
  and = AND , []

  and,and : 0 ⊢ 3 ⟶ 1
  and,and = AND , AND , []

  not,and : 0 ⊢ 2 ⟶ 1
  not,and = NOT , AND , []

  not' : 0 ⊢ 1 ⟶ 1
  not' = NOT , []

  not,not : 0 ⊢ 1 ⟶ 1
  not,not = NOT , NOT , []

  long : 0 ⊢ 0 ⟶ 1
  long = false , NOT , true , AND , []

run : {B B' : ℕ} →
  0 ⊢ B ⟶ B' → Vec Bool B → Vec Bool B'
run [] [] = []

run (_,_ {zero} true d) xs =
  true ∷ run d []
run (_,_ {suc n} true d) xs rewrite lem n =
  run d (true ∷ xs)

run (_,_ {zero} false d) xs =
  false ∷ run d []
run (_,_ {suc n} false d) xs rewrite lem n =
  run d (false ∷ xs)

run (_,_ {zero}  POP d) (x ∷ []) =
  run d []
run (_,_ {suc n} POP d) (x ∷ xs) rewrite lem n =
  run d xs

run (_,_ {zero}  AND d) (x₁ ∷ x₂ ∷ xs) =
  x₂ ∧ x₁ ∷ run d []
run (_,_ {suc n} AND d) (x₁ ∷ x₂ ∷ xs) rewrite lem n =
  run d (x₂ ∧ x₁ ∷ xs)

run (_,_ {zero}  NOT d) (x ∷ []) =
  not x ∷ run d []
run (_,_ {suc n} NOT d) (x ∷ xs) rewrite lem n =
  run d (not x ∷ xs)

