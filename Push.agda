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

run : State → State
run (state [] bs ns) =
  state
  []
  bs
  ns
run (state (lit {EXEC} e ∷ es) bs ns) = run (
  state
  (e ∷ es)
  bs
  ns
  )
run (state (lit {BOOL} b ∷ es) bs ns) = run (
  state
  es
  (b ∷ bs)
  ns
  )
run (state (lit {NAT} n ∷ es) bs ns) = run (
  state
  es
  bs
  (n ∷ ns)
  )
run _ = {!!}

