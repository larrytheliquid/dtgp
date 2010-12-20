module Direct where
open import Data.Nat
open import Data.Bool
open import Data.Vec

infixl 2 _∣_⟶_∣_

data Word : Set where
  Exec-EQ Exec-K
    true false Bool-POP AND NOT : Word

In-Exec : Word → ℕ
In-Exec Exec-EQ = 2
In-Exec Exec-K = 2
In-Exec true = 0
In-Exec false = 0
In-Exec Bool-POP = 0
In-Exec AND = 0
In-Exec NOT = 0

Out-Exec : Word → ℕ
Out-Exec Exec-EQ = 0
Out-Exec Exec-K = 1
Out-Exec true = 0
Out-Exec false = 0
Out-Exec Bool-POP = 0
Out-Exec AND = 0
Out-Exec NOT = 0

In-Bool : Word → ℕ
In-Bool Exec-EQ = 0
In-Bool Exec-K = 0
In-Bool true = 0
In-Bool false = 0
In-Bool Bool-POP = 1
In-Bool AND = 2
In-Bool NOT = 1

Out-Bool : Word → ℕ
Out-Bool Exec-EQ = 1
Out-Bool Exec-K = 0
Out-Bool true = 1
Out-Bool false = 1
Out-Bool Bool-POP = 0
Out-Bool AND = 2
Out-Bool NOT = 1

data _∣_⟶_∣_ : (E B E' B' : ℕ) → Set where
  []  : 0 ∣ 0 ⟶ 0 ∣ 0
  _∷_ : ∀ {E B E' B'} → (w : Word) →
    E ∣ B ⟶ E' ∣ B' →
    In-Exec  w + E  ∣ In-Bool  w + B ⟶
    Out-Exec w + E' ∣ Out-Bool w + B'

