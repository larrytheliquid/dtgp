module TermExamples where
open import Data.Nat
import Term

data Word : Set where
  true false
    not and or
    dup flush
    double
    : Word

In : Word → ℕ → ℕ
In true   B = B
In false  B = B
In not    B = 1 + B
In and    B = 2 + B
In or     B = 2 + B
In dup    B = 1 + B
In flush  B = B
In double B = B

Out : Word → ℕ → ℕ
Out true   B = 1 + B
Out false  B = 1 + B
Out not    B = 1 + B
Out and    B = 1 + B
Out or     B = 1 + B
Out dup    B = 2 + B
Out flush  B = 0
Out double B = 2 * B

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

and∷true∷and∷[] : 2 ⟶ 1
and∷true∷and∷[] = and ∷ true∷and∷[]

long∷[] : 0 ⟶ 1
long∷[] = not ∷ and ∷ and ∷ true ∷ not ∷ false ∷ [ true ]

flush∷long∷[] : 0 ⟶ 0
flush∷long∷[] = flush ∷ long∷[]

dup∷and∷true∷and∷[] : 2 ⟶ 2
dup∷and∷true∷and∷[] = dup ∷ and∷true∷and∷[]

double∷true∷and∷[] : 2 ⟶ 4
double∷true∷and∷[] = double ∷ true∷and∷[]
