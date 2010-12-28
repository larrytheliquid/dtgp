module Take3 where
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (not)
open import Data.Nat hiding (_∸_)
open import Data.List hiding (and)

infixr 5 _,_
infixl 6 _∸_
infixl 6 _∸∸_

_∸_ : ℕ → ℕ → ℕ
zero  ∸ m = zero
m ∸ zero  = m
suc m ∸ suc n = m ∸ n

data Word : Set where
  true not and bool-flush : Word

eq-Word : Word → Word → Bool
eq-Word true true = true
eq-Word not not = true
eq-Word and and = true
eq-Word bool-flush bool-flush = true
eq-Word _ _ = false

Term : Set
Term = List Word

_∸∸_ : Term → Term → Term
[] ∸∸ ys = []
(x ∷ xs) ∸∸ [] = x ∷ xs
(x ∷ xs) ∸∸ (y ∷ ys) with eq-Word x y
... | true = xs ∸∸ ys
... | false = x ∷ xs

data Type (E : Term) (B : ℕ) : Term → Term → ℕ → ℕ → Set where
  true  : Type E B [] (true ∷ []) 0 1
  not   : Type E B [] (not ∷ []) 1 1
  and   : Type E B [] (and ∷ []) 2 1
  bool-flush : Type E B [] (bool-flush ∷ []) B 0

data Deriv : Term → Term → ℕ → ℕ → Set where
  []  : Deriv [] [] 0 0

  _,_ :  ∀ {E E' B B' E-In E-Out B-In B-Out} →
    (w : Type E' B' E-In E-Out B-In B-Out) →
    Deriv E E' B B' →
    Deriv
      (E ++ (E-In ∸∸ E'))
      ((E' ∸∸ E-In) ++ E-Out)
      (B + (B-In ∸ B'))
      ((B' ∸ B-In) + B-Out)

private
  not,[] : Deriv [] (not ∷ []) 1 1
  not,[] = not , []

  and,[] : Deriv [] (and ∷ []) 2 1
  and,[] = and , []

  true,[] : Deriv [] (true ∷ []) 0 1
  true,[] = true , []

  not,not,[] : Deriv [] (not ∷ not ∷ []) 1 1
  not,not,[] = not , not , []

  and,not,[] : Deriv [] (not ∷ and ∷ []) 2 1
  and,not,[] = and , not,[]

  true,and,[] : Deriv [] (and ∷ true ∷ []) 2 2
  true,and,[] = true , and,[]

  and,and,[] : Deriv [] (and ∷ and ∷ []) 3 1
  and,and,[] = and , and,[]

  true,true,[] : Deriv [] (true ∷ true ∷ []) 0 2
  true,true,[] = true , true,[]

  true,true,not,[] : Deriv [] (not ∷ true ∷ true ∷ []) 1 3
  true,true,not,[] = true , true , not , []

  not,true,true,not,[] : Deriv [] (not ∷ true ∷ true ∷ not ∷ []) 1 3
  not,true,true,not,[] = not , true,true,not,[]

  true,and,flush,[] : Deriv [] (bool-flush ∷ and ∷ true ∷ []) 2 2
  true,and,flush,[] = true , and , bool-flush , []

  flush,true,and,[] : Deriv [] (and ∷ true ∷ bool-flush ∷ []) 2 0
  flush,true,and,[] = bool-flush , true,and,[]
