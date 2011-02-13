module Examples.Max where
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Vec
import Stash

data Word : Set where
  two plus times : Word

Type : Set
Type = ℕ × ⊤

In : Word → Type → Type
In two ts = proj₁ ts , _
In plus ts = 2 + proj₁ ts , _
In times ts = 2 + proj₁ ts , _

Out : Word → Type → Type
Out two ts = 1 + proj₁ ts , _
Out plus ts = 1 + proj₁ ts , _
Out times ts = 1 + proj₁ ts , _

open Stash 1 Word In Out

eval : ∀ {ins outs} → Term ins outs → Vec ℕ (proj₁ ins) → Vec ℕ (proj₁ outs)
eval [] as = as
eval (two ∷ xs) as with eval xs as
... | cs = 2 ∷ cs
eval (plus ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ + c₂) ∷ cs
eval (times ∷ xs) as with eval xs as
... | c₂ ∷ c₁ ∷ cs = (c₁ * c₂) ∷ cs

score : Term _ _ → ℕ
score xs = sum (eval xs [])

population : Population (_ , _) (_ , _) _
population =
    (_∷_ {k = _ , _} plus (_∷_ {k = _ , _} plus (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two [])))))
  ∷ (_∷_ {k = _ , _} times (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two [])))
  ∷ (_∷_ {k = _ , _} plus (_∷_ {k = _ , _} times (_∷_ {k = _ , _} two (_∷_ {k = _ , _} times (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two [])))))))
  ∷ (_∷_ {k = _ , _} times (_∷_ {k = _ , _} two (_∷_ {k = _ , _} plus (_∷_ {k = _ , _} two (_∷_ {k = _ , _} two [])))))
  ∷ []

open GP (0 , tt) (1 , tt) score

answer : Population _ _ _
answer = evolve 1337 1 population
