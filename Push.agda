module Push where
open import Data.Bool
open import Data.Nat
open import Data.Nat.DivMod
open import Data.List

infixr 4 _↦_ _↤_
infixr 4 _∷_

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
  _↤_ : U → Type → Type
  _↦_ : U → Type → Type

data Inst : Type → Set where
  NOOP : Inst ★
  POP : {u : U} → Inst (u ↦ ★)
  POPEQ : {u : U} → Inst (u ↦ u ↦ BOOL ↤ ★)
  PLUS MINUS MULT DIV : Inst (NAT ↦ NAT ↦ NAT ↤ ★)
  LT GT : Inst (NAT ↦ NAT ↦ BOOL ↤ ★)
  NOT : Inst (BOOL ↦ BOOL ↤ ★)
  AND OR NAND NOR : Inst (BOOL ↦ BOOL ↦ BOOL ↤ ★)

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

data Stack (u : U) : Set where
  [] : Stack u
  _∷_ : Lit u → Stack u → Stack u

data State : Set where
  state :
    Stack EXEC →
    Stack BOOL →
    Stack NAT →
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

run (state (inst (POP {EXEC}) ∷ _ ∷ es) bs ns) =
  run ( state es bs ns )
run (state (inst (POP {BOOL}) ∷ es) (_ ∷ bs) ns) =
  run ( state es bs ns )
run (state (inst (POP {NAT}) ∷ es) bs (_ ∷ ns)) =
  run ( state es bs ns )

run (state (inst (POPEQ {EXEC}) ∷ e₁ ∷ e₂ ∷ es) bs ns) =
  run ( state es (eq-Lit e₁ e₂ ∷ bs) ns )
run (state (inst (POPEQ {BOOL}) ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (eq-Lit b₁ b₂ ∷ bs) ns )
run (state (inst (POPEQ {NAT}) ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (eq-Lit n₁ n₂ ∷ bs) ns )

run (state (inst PLUS ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₁ + n₂ ∷ ns) )

run (state (inst MINUS ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₁ ∸ n₂ ∷ ns) )

run (state (inst MULT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₁ * n₂ ∷ ns) )

run (state (inst DIV ∷ es) bs (n ∷ zero ∷ ns)) =
  run ( state es bs (n ∷ ns) )
run (state (inst DIV ∷ es) bs (n₁ ∷ (suc n₂) ∷ ns)) =
  run ( state es bs (n₁ div (suc n₂) ∷ ns) )

run (state (inst LT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (n₁ lt n₂ ∷ bs) ns )

run (state (inst GT ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es (n₁ gt n₂ ∷ bs) ns )

run (state (inst NOT ∷ es) (b ∷ bs) ns) =
  run ( state es (not b ∷ bs) ns )

run (state (inst AND ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (b₁ ∧ b₂ ∷ bs) ns )

run (state (inst OR ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (b₁ ∨ b₂ ∷ bs) ns )

run (state (inst NAND ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (not (b₁ ∧ b₂) ∷ bs) ns )

run (state (inst NOR ∷ es) (b₁ ∷ b₂ ∷ bs) ns) =
  run ( state es (not (b₁ ∨ b₂) ∷ bs) ns )

run (state (inst _ ∷ es) bs ns) =
  run ( state es bs ns )

