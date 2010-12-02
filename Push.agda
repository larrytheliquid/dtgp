module Push where
open import Data.Bool
open import Data.Nat
open import Data.List

infixr 4 _↦_ _↤_
infixr 5 _∷_

data U : Set where
  BOOL NAT : U

Lit : U → Set
Lit BOOL = Bool
Lit NAT = ℕ

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

data Expr : Set where
  lit : {u : U} → Lit u → Expr
  inst : {t : Type} → Inst t → Expr

data Stack (u : U) : Set where
  [] : Stack u
  _∷_ : Lit u → Stack u → Stack u

record State : Set where
  field
    EXECS : List Expr
    BOOLS : Stack BOOL
    NATS : Stack NAT


