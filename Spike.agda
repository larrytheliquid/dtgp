module Spike where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_∸_)
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)
-- open import Data.Vec hiding (_++_)
open import Data.Product
open import Data.Maybe

infixl 2 _⊢_⟶_
infixr 5 _∷_ -- _++_
infixl 6 _∸_

_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

data Word (B : ℕ) : ℕ → ℕ → Set where
  true  : Word B 0 1
  not   : Word B 1 1
  and   : Word B 2 1
  dup   : Word B 1 2
  flush : Word B B 0

Req : Set₁
Req = ℕ → ℕ → ℕ → Set

data _⊢_⟶_ (R : Req) : ℕ → ℕ → Set where
  []  : R ⊢ 0 ⟶ 0

  _∷_ : ∀ {B B' In Out} →
    (w : R B' In Out) →
    R ⊢ B ⟶ B' →
    R ⊢ B + (In ∸ B') ⟶ (B' ∸ In) + Out

Term : Req → Set
Term R = ∃₂ (_⊢_⟶_ R)

_++_ : ∀ {R In Out B B'} → R ⊢ In ⟶ Out → R ⊢ B ⟶ B' → R ⊢ B + (In ∸ B') ⟶ (B' ∸ In) + Out
[] ++ ys = {!!}
(x ∷ xs) ++ ys with xs ++ ys
... | ih with x ∷ ih
... | hm = {!!}

-- .B' ∸ .B0 + .B1 != .B1 of type ℕ
-- when checking that the expression ih has type
-- (λ x' x0 x1 → .R x' x0 x1) ⊢ .B + (.B0 ∸ .B') ⟶ .B1

-- xs   : .R ⊢ .B0 ⟶ .B1
-- ys   : .R ⊢ .B ⟶ .B'
-- ih   : .R ⊢ .B + (.B0 ∸ .B') ⟶ .B' ∸ .B0 + .B1
-- x    : .R .B1 .In .Out
-- Goal: .R ⊢ .B + (.B0 + (.In ∸ .B1) ∸ .B') ⟶
--       .B' ∸ (.B0 + (.In ∸ .B1)) + (.B1 ∸ .In + .Out)

-- [] ++ ys = _ , _ , ys
-- (x ∷ xs) ++ ys with xs ++ ys
-- (true ∷ xs) ++ ys | ih = _ , _ , (true ∷ proj₂ (proj₂ ih))
-- (not ∷ xs) ++ ys | ih = _ , _ , (not ∷ proj₂ (proj₂ ih))
-- (and ∷ xs) ++ ys | ih = _ , _ , (and ∷ proj₂ (proj₂ ih))
-- (dup ∷ xs) ++ ys | ih = _ , _ , (dup ∷ proj₂ (proj₂ ih))
-- (flush ∷ xs) ++ ys | ih = _ , _ , (flush ∷ proj₂ (proj₂ ih))

-- Choices : ℕ → ℕ → Set
-- Choices B B' = ∃ (Vec (B ⟶ B'))

-- choices : Term → (B B' : ℕ) → Choices B B'
-- choices (.0 , .0 , []) B B' = _ , []
-- choices (.(B + (In ∸ B')) , .(B' ∸ In + Out) , _∷_ {B} {B'} {In} {Out} w ws) C C'
--   with choices (_ , _ , ws) C C' | C ≟ (B + (In ∸ B')) | C' ≟ (B' ∸ In + Out)
-- ... | _ , ih | yes p | yes p' rewrite p | p' = _ , ((w ∷ ws) ∷ ih)
-- ... | ih | _ | _ = ih

-- choice : (seed B B' : ℕ) → Term → Maybe (B ⟶ B')
-- choice seed B B' t with choices t B B'
-- choice seed 0 0 _ | zero , [] = just []
-- choice seed _ _ _ | zero , [] = nothing
-- ... | suc n , c ∷ cs = just (lookup (seed mod suc n) (c ∷ cs))

-- private
--   not∷[] : 1 ⟶ 1
--   not∷[] = not ∷ []

--   and∷[] : 2 ⟶ 1
--   and∷[] = and ∷ []

--   true∷[] : 0 ⟶ 1
--   true∷[] = true ∷ []

--   not∷not∷[] : 1 ⟶ 1
--   not∷not∷[] = not ∷ not ∷ []

--   and∷not∷[] : 2 ⟶ 1
--   and∷not∷[] = and ∷ not∷[]

--   true∷and∷[] : 2 ⟶ 2
--   true∷and∷[] = true ∷ and∷[]

--   and∷and∷[] : 3 ⟶ 1
--   and∷and∷[] = and ∷ and∷[]

--   true∷true∷[] : 0 ⟶ 2
--   true∷true∷[] = true ∷ true∷[]

--   true∷true∷not∷[] : 1 ⟶ 3
--   true∷true∷not∷[] = true ∷ true ∷ not ∷ []

--   not∷true∷true∷not∷[] : 1 ⟶ 3
--   not∷true∷true∷not∷[] = not ∷ true∷true∷not∷[]

--   true∷and∷flush∷[] : 2 ⟶ 2
--   true∷and∷flush∷[] = true ∷ and ∷ flush ∷ []

--   flush∷true∷and∷[] : 2 ⟶ 0
--   flush∷true∷and∷[] = flush ∷ true∷and∷[]
