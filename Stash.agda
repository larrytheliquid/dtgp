open import Data.Nat
module Stash (W : Set) (In Out : W → ℕ → ℕ) where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; pred)
open import Data.Vec hiding (replicate) renaming (_++_ to _v++_)
open import Data.Product hiding (map)
open import Data.Maybe

data Term : ℕ × ℕ → Set where
  []  : Term (0 , 0)

  cons : ∀ {B} →
    (w : W) → Term B →
    Term (proj₁ B + (In w (proj₂ B) ∸ proj₂ B) ,
    Out w (proj₂ B) + (proj₂ B ∸ In w (proj₂ B)))

import Data.List as L

List-IO : (ws : L.List W) → ℕ × ℕ
List-IO L.[] = 0 , 0
List-IO (L._∷_ w ws) with List-IO ws
... | B =
  proj₁ B + (In w (proj₂ B) ∸ proj₂ B) ,
  Out w (proj₂ B) + (proj₂ B ∸ In w (proj₂ B))

from-List : (ws : L.List W) → Term (List-IO ws)
from-List L.[] = []
from-List (L._∷_ w ws) with from-List ws
... | ih = {!!}
-- cons w ih

IO : ∀ {B} → Term B → ℕ × ℕ
IO [] = 0 , 0
IO (cons w ws) with IO ws
... | B =
  proj₁ B + (In w (proj₂ B) ∸ proj₂ B) ,
  Out w (proj₂ B) + (proj₂ B ∸ In w (proj₂ B))

-- plus : (C B : ℕ × ℕ) → ℕ × ℕ
-- plus (zero , zero) B = B
-- plus C B = (proj₁ C ∸ proj₂ B) + proj₁ B ,
--   (proj₂ B ∸ proj₁ C) + proj₂ C

-- plus : (C B : ℕ × ℕ) → ℕ × ℕ
-- plus (zero , zero) B = B
-- plus (C , C') B = (C ∸ proj₂ B) + proj₁ B ,
--   (proj₂ B ∸ C) + C'


-- append : ∀ {C B} →
--   Term C →
--   Term B →
--   Term (plus C B)
-- append [] ys = ys
-- append (cons x xs) ys with append xs ys
-- ... | ih with cons x ih
-- ... | ret = {!!}

-- _++_ : ∀ {A A' B B'} →
--   A ⟶ A' → B ⟶ B' → Term
-- [] ++ ys = _ , _ , ys
-- (cons x xs) ++ ys with xs ++ ys
-- ... | _ , _ , ih = _ , _ , (cons x xs)

-- Choices : ℕ → ℕ → Set
-- Choices B B' = ∃ (Vec (B ⟶ B'))

-- choices : Term → (B B' : ℕ) → Choices B B'
-- choices (.0 , .0 , []) B B' = _ , []
-- choices (.(B + (In w B' ∸ B')) , .(Out w B' + (B' ∸ In w B')) , _∷_ {B} {B'} w ws) C C'
--   with choices (_ , _ , ws) C C' | C ≟ (B + (In w B' ∸ B')) | C' ≟ (Out w B' + (B' ∸ In w B'))
-- ... | _ , ih | yes p | yes p' rewrite p | p' = _ , ((w ∷ ws) ∷ ih)
-- ... | ih | _ | _ = ih

-- choice : (seed B B' : ℕ) → Term → Maybe (B ⟶ B')
-- choice seed B B' t with choices t B B'
-- choice seed 0 0 _ | zero , [] = just []
-- choice seed _ _ _ | zero , [] = nothing
-- ... | suc n , c ∷ cs = just (lookup (seed mod suc n) (c ∷ cs))

-- crossover : (seed B B' : ℕ) → 
--   (male : Term) → (female : Term) → Term
-- crossover seed B B' male female
--   with choice seed B B' female
-- ... | nothing = male
-- ... | just t = proj₂ (proj₂ male) ++ t

-- Terms : Set
-- Terms = ∃ (Vec Term)

-- distinct-combinations : ℕ → Term → Terms
-- distinct-combinations 0 _ = 1 , (_ , _ , []) ∷ []
-- distinct-combinations n (._ , ._ , []) = 0 , []
-- distinct-combinations (suc n) (._ , ._ , w ∷ ws) =
--   _ ,
--   map (λ x → _ , _ , w ∷ proj₂ (proj₂ x))
--       (proj₂ (distinct-combinations n (_ , _ , ws)))
--   v++
--   proj₂ (distinct-combinations (suc n) (_ , _ , ws))

-- replicate : ℕ → W → Term
-- replicate zero w = _ , _ , w ∷ []
-- replicate (suc n) w with replicate n w
-- ... | _ , _ , ws = _ , _ , w ∷ ws

-- expand : ℕ → Term → Term
-- expand n (._ , ._ , []) = _ , _ , []
-- expand n (._ , ._ , w ∷ ws)
--   with replicate n w | expand n (_ , _ , ws)
-- ... | _ , _ , lhs | _ , _ , rhs = {!!}

-- indistinct-combinations : ℕ → Term → Terms
-- indistinct-combinations n t =
--   distinct-combinations n (expand n t)

-- population : ℕ → Term → Terms
-- population zero t = 0 , []
-- population (suc n) t =
--   _ ,
--   proj₂ (indistinct-combinations (suc n) t)
--   v++
--   proj₂ (population n t)
