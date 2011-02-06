module Push where
open import Data.Bool renaming (not to ¬)
open import Data.Nat
open import Data.List hiding (_++_; and)
open import Data.Vec renaming (_++_ to _v++_)
open import Data.Product hiding (swap)
import Macro

data Word : Set where
  true not and
    add gt
    pop dup depth eq swap
    : Word
  nat : ℕ → Word

Words : Set
Words = List Word

Domain : Set
Domain = Words × ℕ × ℕ

Var : Word → Set
Var true = Domain
Var not = Domain
Var and = Domain
Var (nat _) = Domain
Var add = Domain
Var gt  = Domain
Var pop = Word × Domain
Var dup = Word × Domain
Var depth = Domain
Var eq  = Word × Word × Domain
Var swap = Word × Word × Domain

In : (w : Word) → Var w → Domain
In true    (         ws , m , n) =          ws ,     m ,     n
In not     (         ws , m , n) =          ws , 1 + m ,     n
In and     (         ws , m , n) =          ws , 2 + m ,     n
In (nat _) (         ws , m , n) =          ws ,     m ,     n
In add     (         ws , m , n) =          ws ,     m , 2 + n
In gt      (         ws , m , n) =          ws ,     m , 2 + n
In pop     (w ,      ws , m , n) =          ws ,     m ,     n
In dup     (w ,      ws , m , n) = w ∷ w ∷  ws ,     m ,     n
In depth   (         ws , m , n) =          ws ,     m ,     n
In eq      (w₁ , w₂ , ws , m , n) =          ws ,     m ,     n
In swap    (w₁ , w₂ , ws , m , n) = w₂ ∷ w₁ ∷ ws ,     m ,     n

Out : (w : Word) → Var w → Domain
Out true    (         ws , m , n) = true  ∷          ws , 1 + m ,     n
Out not     (         ws , m , n) = not   ∷          ws , 1 + m ,     n
Out and     (         ws , m , n) = and   ∷          ws , 1 + m ,     n
Out (nat v) (         ws , m , n) = nat v ∷          ws ,     m , 1 + n
Out add     (         ws , m , n) = add   ∷          ws ,     m , 1 + n
Out gt      (         ws , m , n) = gt    ∷          ws , 1 + m ,     n
Out pop     (w ,      ws , m , n) = pop   ∷      w ∷ ws ,     m ,     n
Out dup     (w ,      ws , m , n) = dup   ∷      w ∷ ws ,     m ,     n
Out depth   (         ws , m , n) = depth ∷          ws ,     m , 1 + n
Out eq      (w₁ , w₂ , ws , m , n) = eq    ∷ w₁ ∷ w₂ ∷ ws , 1 + m ,     n
Out swap    (w₁ , w₂ , ws , m , n) = swap  ∷ w₁ ∷ w₂ ∷ ws ,     m ,     n

open Macro Domain Word Var In Out

Closed : Words → ℕ → ℕ → Set
Closed ws m n = Term ([] , 0 , 0) (ws , m , n)

sukitrebek : Closed (true ∷ []) 1 0
sukitrebek = cons true {_ , _ , _} nil

sukitrebek2 : Closed (depth ∷ true ∷ []) 1 1
sukitrebek2 = cons depth {_ , _ , _} (cons true {_ , _ , _} nil)

sukitrebek3 : Closed (swap ∷ true ∷ not ∷ []) 1 0
sukitrebek3 = cons swap {_ , _ , _ , _ , _} (cons not {_ , _ , _} (cons true {_ , _ , _} nil))
