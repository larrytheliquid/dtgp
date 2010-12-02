module Push where
open import Data.Bool
open import Data.Nat
open import Data.List

infixr 4 _↦_ _↤_
infixr 5 _∷_

data U : Set where
  EXEC : U
  BOOL NAT : U

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

record State : Set where
  field
    EXECS : Stack EXEC
    BOOLS : Stack BOOL
    NATS : Stack NAT
open State

run : State → State
run st with EXECS st
run st | [] = record
  { EXECS = []
  ; BOOLS = BOOLS st
  ; NATS = NATS st
  }
run st | (lit {BOOL} l ∷ es) = record
  { EXECS = es
  ; BOOLS = l ∷ BOOLS st
  ; NATS = NATS st
  }
run st | (lit {NAT} l ∷ es) = record
  { EXECS = es
  ; BOOLS = BOOLS st
  ; NATS = l ∷ NATS st
  }
run st | (lit {EXEC} l ∷ es) = record
  { EXECS = l ∷ es
  ; BOOLS = BOOLS st
  ; NATS = NATS st
  }
run st | inst i ∷ es = {!!}

