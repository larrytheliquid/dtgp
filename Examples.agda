module Examples where
open import Data.Nat
import Stash

data Word : Set where
  true not and dup flush : Word

In : Word → ℕ → ℕ
In true  B = 0
In not   B = 1
In and   B = 2
In dup   B = 1
In flush B = B

Out : Word → ℕ → ℕ
Out true  B = 1
Out not   B = 1
Out and   B = 1
Out dup   B = 2
Out flush B = 0

open Stash Word In Out

private
  not∷[] : 1 ⟶ 1
  not∷[] = not ∷ []

  and∷[] : 2 ⟶ 1
  and∷[] = and ∷ []

  true∷[] : 0 ⟶ 1
  true∷[] = true ∷ []

  not∷not∷[] : 1 ⟶ 1
  not∷not∷[] = not ∷ not ∷ []

  and∷not∷[] : 2 ⟶ 1
  and∷not∷[] = and ∷ not∷[]

  true∷and∷[] : 2 ⟶ 2
  true∷and∷[] = true ∷ and∷[]

  and∷and∷[] : 3 ⟶ 1
  and∷and∷[] = and ∷ and∷[]

  true∷true∷[] : 0 ⟶ 2
  true∷true∷[] = true ∷ true∷[]

  true∷true∷not∷[] : 1 ⟶ 3
  true∷true∷not∷[] = true ∷ true ∷ not ∷ []

  not∷true∷true∷not∷[] : 1 ⟶ 3
  not∷true∷true∷not∷[] = not ∷ true∷true∷not∷[]

  true∷and∷flush∷[] : 2 ⟶ 2
  true∷and∷flush∷[] = true ∷ and ∷ flush ∷ []

  flush∷true∷and∷[] : 2 ⟶ 0
  flush∷true∷and∷[] = flush ∷ true∷and∷[]
