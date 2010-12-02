module Push where
open import Data.Bool
open import Data.Nat
open import Data.List

infixr 4 _↦_ _↤_
infixr 5 _∷_

data U : Set where
  EXEC BOOL NAT : U

data Type : Set where
  ★ : Type
  _↤_ : U → Type → Type
  _↦_ : U → Type → Type

data Inst : Type → Set where
  NOOP : Inst ★
  POP : {u : U} → Inst (u ↦ ★)
  DUP : {u : U} → Inst (u ↦ u ↤ ★)
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

data Stack (u : U) : Set where
  [] : Stack u
  _∷_ : Lit u → Stack u → Stack u

data State : Set where
  state :
    Stack EXEC →
    Stack BOOL →
    Stack NAT →
    State

run-lit : {u : U} → Lit u → State → State
run-lit {EXEC} e (state es bs ns) =
  state (e ∷ es) bs ns
run-lit {BOOL} b (state es bs ns) =
  state es (b ∷ bs) ns
run-lit {NAT} n (state es bs ns) =
  state es bs (n ∷ ns)

run : State → State

run (state [] bs ns) =
  state [] bs ns

run (state (lit {EXEC} e ∷ es) bs ns) =
  run ( state (e ∷ es) bs ns )

run (state (lit {BOOL} b ∷ es) bs ns) =
  run ( state es (b ∷ bs) ns )

run (state (lit {NAT} n ∷ es) bs ns) =
  run ( state es bs (n ∷ ns) )

run (state (inst NOOP ∷ es) bs ns) =
  run ( state es bs ns )

run (state (inst (POP {EXEC}) ∷ (e ∷ es)) bs ns) =
  run ( state es bs ns )
run (state (inst (POP {BOOL}) ∷ es) (b ∷ bs) ns) =
  run ( state es bs ns )
run (state (inst (POP {NAT}) ∷ es) bs (n ∷ ns)) =
  run ( state es bs ns )
run (state (inst POP ∷ es) bs ns) =
  run ( state es bs ns )

run (state (inst DUP ∷ es) bs ns) = {!!}

run (state (inst POPEQ ∷ es) bs ns) = {!!}

run (state (inst PLUS ∷ es) bs (n₁ ∷ n₂ ∷ ns)) =
  run ( state es bs (n₁ + n₂ ∷ ns) )
run (state (inst PLUS ∷ es) bs ns) =
  run ( state es bs ns )

run (state (inst MINUS ∷ es) bs ns) = {!!}

run (state (inst MULT ∷ es) bs ns) = {!!}

run (state (inst DIV ∷ es) bs ns) = {!!}

run (state (inst LT ∷ es) bs ns) = {!!}

run (state (inst GT ∷ es) bs ns) = {!!}

run (state (inst NOT ∷ es) bs ns) = {!!}

run (state (inst AND ∷ es) bs ns) = {!!}

run (state (inst OR ∷ es) bs ns) = {!!}

run (state (inst NAND ∷ es) bs ns) = {!!}

run (state (inst NOR ∷ es) bs ns) = {!!}


