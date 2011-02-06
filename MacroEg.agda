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
In true (ws , n) = ws , n
In not (ws , n) = ws , 1 + n
In and (ws , n) = ws , 2 + n
In pop (w , ws , n) = ws , n
In dup (w , ws , n) = w ∷ w ∷ ws , n

Out : (w : Word) → Var w → Domain
Out true (ws , n) = true ∷ ws , 1 + n
Out not (ws , n) = not ∷ ws , 1 + n
Out and (ws , n) = and ∷ ws , 1 + n
Out pop (w , ws , n) = pop ∷ w ∷ ws , n
Out dup (w , ws , n) = dup ∷ w ∷ ws , n

open Macro Domain Word Var In Out

Closed : Words → ℕ → Set
Closed ws n = Term ([] , 0) (ws , n)

sukitrebek : Closed (true ∷ []) 1
sukitrebek = cons true {_ , _} nil

sukitrebek2 : Closed (pop ∷ true ∷ []) 0
sukitrebek2 = cons pop {_ , _ , _} nil

sukitrebek3 : Closed (not ∷ true ∷ []) 1
sukitrebek3 = cons not {_ , _} (cons true {_ , _} nil)

sukitrebek4 : Closed (true ∷ true ∷ []) 2
sukitrebek4 = cons true {_ , _} (cons true {_ , _} nil)

sukitrebek5 : Closed (true ∷ true ∷ true ∷ []) 3
sukitrebek5 = cons true {_ , _} (cons true {_ , _} (cons true {_ , _} nil))

sukitrebek6 : Closed (and ∷ true ∷ true ∷ []) 1
sukitrebek6 = cons and {_ , _} (cons true {_ , _} (cons true {_ , _} nil))

sukitrebek7 : Closed (dup ∷ true ∷ []) 2
sukitrebek7 = cons dup {_ , _ , _} (cons true {_ , _} (cons true {_ , _} nil))

sukitrebek8 : Closed (not ∷ not ∷ true ∷ []) 1
sukitrebek8 = cons not {_ , _} (cons not {_ , _} (cons true {_ , _} nil))

sukitrebek9 : Closed (dup ∷ not ∷ true ∷ []) 1
sukitrebek9 = cons dup {_ , _ , _} (cons not {_ , _} (cons not {_ , _} (cons true {_ , _} nil)))

