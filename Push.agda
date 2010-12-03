module Push where
open import Data.Bool
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality

infixr 4 _↦_ _↤_

_lt_ : ℕ → ℕ → Bool
zero lt (suc n) = true
(suc n) lt (suc m) = n lt m
_ lt _ = false

_gt_ : ℕ → ℕ → Bool
(suc n) gt zero = true
(suc n) gt (suc m) = n gt m
_ gt _ = false

data U : Set where
  EXEC BOOL NAT : U

data Type : Set where
  ★ : Type
  _↤_ : Type → U → Type
  _↦_ : U → Type → Type

data Inst : Type → Set where
  NOOP : Inst ★
  POP : (u : U) → Inst (u ↦ ★)
  EQ : (u : U) → Inst (u ↦ u ↦ ★ ↤ BOOL)
  ADD SUB MULT DIV : Inst (NAT ↦ NAT ↦ ★ ↤ NAT)
  LT GT : Inst (NAT ↦ NAT ↦ ★ ↤ BOOL)
  NOT : Inst (BOOL ↦ ★ ↤ BOOL)
  AND OR NAND NOR : Inst (BOOL ↦ BOOL ↦ ★ ↤ BOOL)

mutual
  Lit : U → Set
  Lit EXEC = Expr
  Lit BOOL = Bool
  Lit NAT = ℕ

  data Expr : Set where
    lit : {u : U} → Lit u → Expr
    inst : {t : Type} → Inst t → Expr

postulate
  eq-Lit : {u : U} → Lit u → Lit u → Bool

Stack : (u : U) → ℕ → Set
Stack u = Vec (Lit u)

data State : Set where
  state : {x y z : ℕ} →
    Stack EXEC x →
    Stack BOOL y →
    Stack NAT z →
    State

run : State → State

run (state [] bs ns) =
  state [] bs ns

run (state (lit {EXEC} e ∷ es) bs ns) =
  run ( state (e ∷ es) bs ns )

run (state (lit {BOOL} b ∷ es) bs ns) =
  run ( state es (b ∷ bs) ns )

run (state (lit {NAT} n ∷ es) bs ns) =
  run ( state es bs (n ∷ ns) )

run (state (inst (POP EXEC) ∷ _ ∷ es) bs ns) =
  run ( state es bs ns )
run (state (inst (POP BOOL) ∷ es) (_ ∷ bs) ns) =
  run ( state es bs ns )
run (state (inst (POP NAT) ∷ es) bs (_ ∷ ns)) =
  run ( state es bs ns )

run (state (inst (EQ EXEC) ∷ e₁ ∷ e₂ ∷ es) bs ns) =
  run ( state es (eq-Lit e₂ e₁ ∷ bs) ns )
run (state (inst (EQ BOOL) ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (eq-Lit b₂ b₁ ∷ bs) ns )
run (state (inst (EQ NAT) ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (eq-Lit n₂ n₁ ∷ bs) ns )

run (state (inst ADD ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₂ + n₁ ∷ ns) )

run (state (inst SUB ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₂ ∸ n₁ ∷ ns) )

run (state (inst MULT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₂ * n₁ ∷ ns) )

run (state (inst DIV ∷ es) bs ((suc n₁) ∷ n₂ ∷ ns)) =
  run ( state es bs (n₂ div (suc n₁) ∷ ns) )

run (state (inst LT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (n₂ lt n₁ ∷ bs) ns )

run (state (inst GT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (n₂ gt n₁ ∷ bs) ns )

run (state (inst NOT ∷ es) (b ∷ bs) ns) =
  run ( state es (not b ∷ bs) ns )

run (state (inst AND ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (b₂ ∧ b₁ ∷ bs) ns )

run (state (inst OR ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es ((b₂ ∨ b₁) ∷ bs) ns )

run (state (inst NAND ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (not (b₂ ∧ b₁) ∷ bs) ns )

run (state (inst NOR ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (not (b₂ ∨ b₁) ∷ bs) ns )

run (state (inst _ ∷ es) bs ns) =
  run ( state es bs ns )

prog1 : Stack EXEC 8
prog1 = lit 5 ∷ lit 4 ∷ inst DIV ∷ lit 7 ∷ inst ADD ∷ lit 2 ∷ lit 3 ∷ inst GT ∷ []

test1 : state [] (false ∷ []) (8 ∷ []) ≡ run (state prog1 [] [])
test1 = refl

prog2 : Stack EXEC 3
prog2 = inst (POP EXEC) ∷ lit 3 ∷ lit 3 ∷ []

test2 : state [] [] (3 ∷ []) ≡ run (state prog2 [] [])
test2 = refl
