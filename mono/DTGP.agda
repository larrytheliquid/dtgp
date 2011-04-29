open import Data.Nat hiding (_≥_)
module DTGP (Word : Set) (pre post : Word → ℕ → ℕ) where
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_)
open import Data.Fin hiding (_+_; raise)
open import Data.Maybe
open import Data.Product hiding (map; swap)
open import Data.List hiding (length) renaming (_++_ to _l++_)
open import Data.Vec hiding (_++_; _>>=_; concat; map; init)
open import DTGP.Rand

infixr 5 _∷_ _++_ _++'_

data Term (inp : ℕ) : ℕ → Set where
  []  : Term inp inp

  _∷_ : ∀ {n} (w : Word) →
    Term inp (pre w n) → Term inp (post w n)

_++_ : ∀ {inp mid out} →
  Term mid out →
  Term inp mid →
  Term inp out
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {inp out} mid : Term inp out → Set where
  _++'_ :
    (xs : Term mid out)
    (ys : Term inp mid) →
    Split mid (xs ++ ys)

swap₁ : ∀ {inp mid out} {xs ys : Term inp out} →
  Split mid xs → Split mid ys → Term inp out
swap₁ (xs ++' ys) (as ++' bs) = xs ++ bs

swap₂ : ∀ {inp mid out} {xs ys : Term inp out} →
  Split mid xs → Split mid ys → Term inp out
swap₂ (xs ++' ys) (as ++' bs) = as ++ ys

swaps : ∀ {inp mid out} {xs ys : Term inp out} →
  Split mid xs → Split mid ys →
  Term inp out × Term inp out
swaps xs ys = swap₁ xs ys , swap₂ xs ys

split : ∀ {inp out} (n : ℕ) (xs : Term inp out) → ∃ λ mid → Split mid xs
split zero xs = _ , [] ++' xs
split (suc n) [] = _ , [] ++' []
split (suc n) (x ∷ xs) with split n xs
split (suc n) (x ∷ ._) | _ , xs ++' ys = _ , (x ∷ xs) ++' ys

splits : ∀ {inp out} (n : ℕ) mid → (xs : Term inp out) → ∃ (Vec (Split mid xs))
splits zero mid xs with split zero xs
... | mid' , ys with mid ≟ mid'
... | yes p rewrite p = _ , ys ∷ []
... | no p = _ , []
splits (suc n) mid xs with split (suc n) xs
... | mid' , ys with mid ≟ mid' | splits n mid xs
... | yes p | _ , yss rewrite p = _ , ys ∷ yss
... | no p | _ , yss = _ , yss

length : ∀ {inp out} → Term inp out → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

split♀ : ∀ {inp out} → (xs : Term inp out) → Rand (∃ λ mid → Split mid xs)
split♀ xs = 
  rand >>= λ r →
  let i = r mod (suc (length xs))
  in return (split (toℕ i) xs)

split♂ : ∀ {inp out} (xs : Term inp out) mid →
  Maybe (Rand (Split mid xs))
split♂ xs B
  with splits (length xs) B xs
... | zero , [] = nothing
... | suc n , xss = just (
  rand >>= λ r →
  return (lookup (r mod suc n) xss)
 )

crossover : ∀ {inp out} (♀ ♂ : Term inp out) →
  Rand (Term inp out × Term inp out)
crossover ♀ ♂ =
  split♀ ♀ >>= λ b,xs →
  maybe′
    (_=<<_ (return ∘ (swaps (proj₂ b,xs))))
    (return (♀ , ♂))
    (split♂ ♂ (proj₁ b,xs))

Population : ∀ inp out n → Set
Population inp out n = Vec (Term inp out) (2 + n)

module Initialization
  (match : ∀ w out → Dec (Σ ℕ λ n → out ≡ pre w n))
  where

  toMaybe : ∀ {w inp out} →
    Term inp out →
    Dec (∃ λ n → out ≡ pre w n) →
    Maybe (∃ λ n → Term inp n)
  toMaybe {w = w} ws (no _) = nothing
  toMaybe {w = w} ws (yes (_ , p))
    rewrite p = just (_ , w ∷ ws)

  enum-inp : ∀ (n : ℕ) inp → List Word → List (Σ ℕ λ out → Term inp out)
  enum-inp zero inp ws = gfilter (λ w → toMaybe [] (match w inp)) ws
  enum-inp (suc n) A ws
    with enum-inp n A ws
  ... | ih = concat (map (λ out,t → gfilter (λ w →
    toMaybe (proj₂ out,t) (match w (proj₁ out,t))
      ) ws) ih) l++ ih

  filter-out : ∀ {inp} out → List (∃ (Term inp)) → List (Term inp out)
  filter-out out [] = []
  filter-out out ((out' , x) ∷ xs)
    with out' ≟ out
  ... | no p = filter-out out xs
  ... | yes p rewrite p = x ∷ filter-out out xs

  init : ∀ (n : ℕ) inp out → List Word → List (Term inp out)
  init n inp out ws = filter-out out (enum-inp n inp ws)

module Evolution {inp out} (score : Term inp out → ℕ) where

  _≥_ : ℕ → ℕ → Bool
  zero ≥ zero = true
  zero ≥ (suc n) = false
  (suc m) ≥ zero = true
  (suc m) ≥ (suc n) = m ≥ n

  select : ∀ {n} →
    Population inp out n → Rand (Term inp out)
  select {n = n} xss =
    rand >>= λ ii →
    rand >>= λ jj →
    let ♀ = lookup (ii mod (2 + n)) xss
        ♂ = lookup (jj mod (2 + n)) xss
    in return $
      if score ♀ ≥ score ♂
      then ♀ else ♂

  breed2 : ∀ {n} →
    Population inp out n →
    Rand (Term inp out × Term inp out)
  breed2 xss =
    select xss >>= λ ♀ →
    select xss >>= λ ♂ →
    crossover ♀ ♂

  breedN : ∀ {m} → (n : ℕ) →
    Population inp out m →
    Rand (Vec (Term inp out) n)
  breedN zero xss = return []
  breedN (suc n) xss =
    breed2 xss >>= λ offspring →
    breedN n xss >>= λ ih →
    return (proj₁ offspring ∷ ih)

  evolve1 : ∀ {n} →
    Population inp out n → Rand (Population inp out n)
  evolve1 xss = breedN _ xss

  evolveN : ∀ {n} → (gens : ℕ) →
    Population inp out n → Rand (Population inp out n)
  evolveN zero xss = return xss
  evolveN (suc gens) xss =
    evolveN gens xss >>= evolve1

  evolve : ∀ {n} → (seed gens : ℕ) →
    Population inp out n → Population inp out n
  evolve seed gens xss =
    runRand (evolveN gens xss) seed

