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

  true∷[]' : run true∷[] [] ≡ (true ∷ [])
  true∷[]' = refl

  not∷not∷[] : 1 ⟶ 1
  not∷not∷[] = not ∷ not ∷ []

  not∷not∷[]' : run not∷not∷[] (false ∷ []) ≡ (false ∷ [])
  not∷not∷[]' = refl

  and∷not∷[] : 2 ⟶ 1
  and∷not∷[] = and ∷ not∷[]

  and∷not∷[]' : run and∷not∷[] (true ∷ false ∷ []) ≡ (true ∷ [])
  and∷not∷[]' = refl

  true∷and∷[] : 2 ⟶ 2
  true∷and∷[] = true ∷ and∷[]

  true∷and∷[]' : run true∷and∷[] (false ∷ true ∷ []) ≡ (true ∷ false ∷ [])
  true∷and∷[]' = refl

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

