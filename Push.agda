module Push where
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Vec

infixr 4 _↦_
infixr 5 _∷_

data U : Set where
  BOOL NAT : U

Lit : U → Set
Lit BOOL = Bool
Lit NAT = ℕ

data Type : Set where
  _★ : U → Type
  _↦_ : U → Type → Type

data Inst : Type → Set where
  PLUS MINUS MULT DIV : Inst (NAT ↦ NAT ↦ NAT ★)

data Expr : U → Set where
  lit : {u : U} → Lit u → Expr u
  inst : {u : U} {t : Type} → Inst (u ↦ t) → Expr u

data Stack : U → Set where
  [] : {u : U} → Stack u
  _∷_ : {u : U} → Expr u → Stack u → Stack u

record State : Set where
  field
    BOOLS : Stack BOOL
    NATS : Stack NAT


