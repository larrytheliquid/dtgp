module TermExamples where
open import Data.Nat
import Term

data Word : Set where
  true false
    not and or
    dup flush
    square
    : Word

In : Word → ℕ → ℕ
In true   B = B
In false  B = B
In not    B = 1 + B
In and    B = 2 + B
In or     B = 2 + B
In dup    B = 1 + B
In flush  B = B
In square B = B

Out : Word → ℕ → ℕ
Out true   B = 1 + B
Out false  B = 1 + B
Out not    B = 1 + B
Out and    B = 1 + B
Out or     B = 1 + B
Out dup    B = 2 + B
Out flush  B = 0
Out square B = B * B

open Term Word In Out

not∷[] : 1 ⟶ 1
not∷[] = [ not ]

and∷[] : 2 ⟶ 1
and∷[] = [ and ]

true∷[] : 0 ⟶ 1
true∷[] = [ true ]

not∷not∷[] : 1 ⟶ 1
not∷not∷[] = not ∷ not ∷ []

true∷and∷[] : 2 ⟶ 2
true∷and∷[] = true ∷ and∷[]

false∷true∷and∷[] : 2 ⟶ 3
false∷true∷and∷[] = false ∷ true∷and∷[]

and∷true∷and∷[] : 2 ⟶ 1
and∷true∷and∷[] = and ∷ true∷and∷[]

long∷[] : 0 ⟶ 1
long∷[] = not ∷ and ∷ and ∷ true ∷ not ∷ false ∷ [ true ]

flush∷long∷[] : 0 ⟶ 0
flush∷long∷[] = flush ∷ long∷[]

dup∷and∷true∷and∷[] : 2 ⟶ 2
dup∷and∷true∷and∷[] = dup ∷ and∷true∷and∷[]

square∷false∷true∷and∷[] : 2 ⟶ 9
square∷false∷true∷and∷[] = square ∷ false∷true∷and∷[]
