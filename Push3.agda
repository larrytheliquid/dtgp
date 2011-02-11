module Push3 where
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

Domain : Set
Domain = ℕ × ℕ × ℕ

Var : Word → Set
Var true = Domain
Var not = Domain
Var and = Domain
Var (nat _) = Domain
Var add = Domain
Var gt  = Domain
Var pop = Domain
Var dup = Domain
Var depth = Domain
Var eq  = Domain
Var swap = Domain

In : (w : Word) → Var w → Domain
In true    (         ws , m , n) =          ws ,     m ,     n
In not     (         ws , m , n) =          ws , 1 + m ,     n
In and     (         ws , m , n) =          ws , 2 + m ,     n
In (nat _) (         ws , m , n) =          ws ,     m ,     n
In add     (         ws , m , n) =          ws ,     m , 2 + n
In gt      (         ws , m , n) =          ws ,     m , 2 + n
In pop     (      ws , m , n) =          ws ,     m ,     n
In dup     (      ws , m , n) = 2 +  ws ,     m ,     n
In depth   (         ws , m , n) =          ws ,     m ,     n
In eq      (ws , m , n) =          ws ,     m ,     n
In swap    (ws , m , n) = 2 + ws ,     m ,     n

Out : (w : Word) → Var w → Domain
Out true    (         ws , m , n) = 1 +          ws , 1 + m ,     n
Out not     (         ws , m , n) = 1 +          ws , 1 + m ,     n
Out and     (         ws , m , n) = 1 +          ws , 1 + m ,     n
Out (nat v) (         ws , m , n) = 1 +          ws ,     m , 1 + n
Out add     (         ws , m , n) = 1 +          ws ,     m , 1 + n
Out gt      (         ws , m , n) = 1 +          ws , 1 + m ,     n
Out pop     (      ws , m , n) = 2 + ws ,     m ,     n
Out dup     (      ws , m , n) = 2 + ws ,     m ,     n
Out depth   (         ws , m , n) = 1 +          ws ,     m , 1 + n
Out eq      (ws , m , n) = 3 + ws , 1 + m ,     n
Out swap    (ws , m , n) = 3 + ws ,     m ,     n

open Macro Domain Word Var In Out

Closed : ℕ → ℕ → ℕ → Set
Closed ws m n = Term (0 , 0 , 0) (ws , m , n)

sukitrebek : Closed 1 1 0
sukitrebek = cons true {_ , _ , _} nil

sukitrebek2 : Closed 2 1 1
sukitrebek2 = cons depth {_ , _ , _} (cons true {_ , _ , _} nil)

sukitrebek3 : Closed 3 1 0
sukitrebek3 = cons swap {_ , _ , _} (cons not {_ , _ , _} (cons true {_ , _ , _} nil))

sukitrebek4 : Closed 2 0 0
sukitrebek4 = cons pop {_ , _ , _} (cons true {_ , _ , _} nil)
