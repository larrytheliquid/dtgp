module MacroEg where
open import Data.Bool renaming (not to ¬)
open import Data.Nat
open import Data.List hiding (_++_; and)
open import Data.Vec renaming (_++_ to _v++_)
open import Data.Product
import Macro

data Word : Set where
  true not and pop dup : Word

Words : Set
Words = List Word

Domain : Set
Domain = Words × ℕ

Var : Word → Set
Var true = Domain
Var not = Domain
Var and = Domain
Var pop = Word × Domain
Var dup = Word × Domain

In : (w : Word) → Var w → Domain
In true (ws , n) = true ∷ ws , n
In not (ws , n) = not ∷ ws , 1 + n
In and (ws , n) = and ∷ ws , 2 + n
In pop (w , ws , n) = pop ∷ w ∷ ws , n
In dup (w , ws , n) = dup ∷ w ∷ ws , n

Out : (w : Word) → Var w → Domain
Out true (ws , n) = ws , 1 + n
Out not (ws , n) = ws , 1 + n
Out and (ws , n) = ws , 1 + n
Out pop (w , ws , n) = ws , n
Out dup (w , ws , n) = w ∷ w ∷ ws , n

open Macro Domain Word Var In Out

Closed : Words → ℕ → Set
Closed ws n = Term (ws , 0) ([] , n)

sukitrebek : Closed (true ∷ []) 1
sukitrebek = _∷_ true {[] , 0} []

sukitrebek2 : Closed (pop ∷ true ∷ []) 0
sukitrebek2 = _∷_ pop {true , [] , 0} []

