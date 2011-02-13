module Examples.ArithmeticExpressions where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product hiding (map)
open import Data.Vec
import Stash

data Word : Set where
  true zero : Word
  not suc : Word
  and plus : Word
  nateq booleq : Word

Type : Set
Type = ℕ × ℕ × ⊤

In : Word → Type → Type
In true   (b , n , tt) = b , n , tt
In zero   (b , n , tt) = b , n , tt
In not    (b , n , tt) = 1 + b , n , tt
In suc    (b , n , tt) = b , 1 + n , tt
In and    (b , n , tt) = 2 + b , n , tt
In plus   (b , n , tt) = b , 2 + n , tt
In nateq  (b , n , tt) = b , 2 + n , tt
In booleq (b , n , tt) = 2 + b , n , tt

Out : Word → Type → Type
Out true   (b , n , tt) = 1 + b , n , tt
Out zero   (b , n , tt) = b , 1 + n , tt
Out not    (b , n , tt) = 1 + b , n , tt
Out suc    (b , n , tt) = b , 1 + n , tt
Out and    (b , n , tt) = 1 + b , n , tt
Out plus   (b , n , tt) = b , 1 + n , tt
Out nateq  (b , n , tt) = 1 + b , n , tt
Out booleq (b , n , tt) = b , 1 + n , tt

open Stash 2 Word In Out

eval : ∀ {ins outs} → Term ins outs → Vec ℕ (proj₁ ins) → Vec ℕ (proj₁ (proj₂ ins)) →
  Vec Bool (proj₁ outs) × Vec ℕ (proj₁ (proj₂ outs))
eval [] bs ns = ?
eval (true ∷ xs) bs ns with eval xs bs ns
... | bs' , ns' = (true ∷ bs') , ns'
eval (_ ∷ xs) bs ns = ?
-- ... | c₂ ∷ c₁ ∷ cs = (c₁ + c₂) ∷ cs
-- eval (times ∷ xs) as with eval xs as
-- ... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs


