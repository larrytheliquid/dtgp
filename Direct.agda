module Direct where
open import Data.Nat
open import Data.Bool
open import Data.Vec

infixl 2 _⟶_
infixr 5 _,_

data Word : Set where
  Exec-EQ Exec-K
    true false Bool-POP Bool-DUP AND NOT : Word

In-Exec : Word → ℕ
In-Exec Exec-EQ = 2
In-Exec Exec-K = 2
In-Exec true = 0
In-Exec false = 0
In-Exec Bool-POP = 0
In-Exec Bool-DUP = 0
In-Exec AND = 0
In-Exec NOT = 0

Out-Exec : Word → ℕ
Out-Exec Exec-EQ = 0
Out-Exec Exec-K = 1
Out-Exec true = 0
Out-Exec false = 0
Out-Exec Bool-POP = 0
Out-Exec Bool-DUP = 0
Out-Exec AND = 0
Out-Exec NOT = 0

In-Bool : Word → ℕ
In-Bool Exec-EQ = 0
In-Bool Exec-K = 0
In-Bool true = 0
In-Bool false = 0
In-Bool Bool-POP = 1
In-Bool Bool-DUP = 1
In-Bool AND = 2
In-Bool NOT = 1

Out-Bool : Word → ℕ
Out-Bool Exec-EQ = 1
Out-Bool Exec-K = 0
Out-Bool true = 1
Out-Bool false = 1
Out-Bool Bool-POP = 0
Out-Bool Bool-DUP = 2
Out-Bool AND = 1
Out-Bool NOT = 1

data _⟶_ : (B B' : ℕ) → Set where
  []  : 0 ⟶ 0
  _,_ : ∀ {B B'} → (w : Word) →
    B ⟶ B' →
    In-Bool w + (B ∸ Out-Bool w) ⟶
    B' + (Out-Bool w ∸ B)

private
  dup,dup : 1 ⟶ 3
  dup,dup = Bool-DUP , Bool-DUP , []

  and,and : 3 ⟶ 1
  and,and = AND , AND , []

  not,and : 2 ⟶ 1
  not,and = NOT , AND , []

  not,not : 1 ⟶ 1
  not,not = NOT , NOT , []

  long : 0 ⟶ 1
  long = false , NOT , true , AND , []


