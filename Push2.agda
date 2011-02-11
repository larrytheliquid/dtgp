module Push2 where
open import Data.Bool renaming (not to ¬)
open import Data.Nat
open import Data.List hiding (_++_; and)
open import Data.Vec renaming (_++_ to _v++_)
open import Data.Product hiding (swap)
open import Data.Unit
import Macro

data Word : Set where
  true not and
    add gt
    pop dup depth eq swap
    : Word
  nat : ℕ → Word

Words : Set
Words = List ⊤

Domain : Set
Domain = Words × ℕ × ℕ

Var : Word → Set
Var true = Domain
Var not = Domain
Var and = Domain
Var (nat _) = Domain
Var add = Domain
Var gt  = Domain
Var pop = ⊤ × Domain
Var dup = ⊤ × Domain
Var depth = Domain
Var eq  = ⊤ × ⊤ × Domain
Var swap = ⊤ × ⊤ × Domain

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
Out true    (         ws , m , n) = tt  ∷          ws , 1 + m ,     n
Out not     (         ws , m , n) = tt   ∷          ws , 1 + m ,     n
Out and     (         ws , m , n) = tt   ∷          ws , 1 + m ,     n
Out (nat v) (         ws , m , n) = tt ∷          ws ,     m , 1 + n
Out add     (         ws , m , n) = tt   ∷          ws ,     m , 1 + n
Out gt      (         ws , m , n) = tt    ∷          ws , 1 + m ,     n
Out pop     (w ,      ws , m , n) = tt   ∷      w ∷ ws ,     m ,     n
Out dup     (w ,      ws , m , n) = tt   ∷      w ∷ ws ,     m ,     n
Out depth   (         ws , m , n) = tt ∷          ws ,     m , 1 + n
Out eq      (w₁ , w₂ , ws , m , n) = tt    ∷ w₁ ∷ w₂ ∷ ws , 1 + m ,     n
Out swap    (w₁ , w₂ , ws , m , n) = tt  ∷ w₁ ∷ w₂ ∷ ws ,     m ,     n

open Macro Domain Word Var In Out

Closed : Words → ℕ → ℕ → Set
Closed ws m n = Term ([] , 0 , 0) (ws , m , n)

sukitrebek : Closed (tt ∷ []) 1 0
sukitrebek = cons true {_ , _ , _} nil

sukitrebek2 : Closed (tt ∷ tt ∷ []) 1 1
sukitrebek2 = cons depth {_ , _ , _} (cons true {_ , _ , _} nil)

sukitrebek3 : Closed (tt ∷ tt ∷ tt ∷ []) 1 0
sukitrebek3 = cons swap {_ , _ , _ , _ , _} (cons not {_ , _ , _} (cons true {_ , _ , _} nil))
