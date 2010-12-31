module Examples where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat
open import Data.Vec
import Stash
open import Syntax
open Stash Word In Out
open import Semantics

private
  not∷[] : 1 ⟶ 1
  not∷[] = not ∷ []

  not∷[]' : run not∷[] (false ∷ []) ≡ (true ∷ [])
  not∷[]' = refl

  and∷[] : 2 ⟶ 1
  and∷[] = and ∷ []

  and∷[]' : run and∷[] (true ∷ true ∷ []) ≡ (true ∷ [])
  and∷[]' = refl

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

