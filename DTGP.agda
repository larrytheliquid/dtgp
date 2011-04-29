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

data Term (ins : ℕ) : ℕ → Set where
  []  : Term ins ins

  _∷_ : ∀ {n} →
    (w : Word) → Term ins (pre w n) →
    Term ins (post w n)

_++_ : ∀ {ins mid outs} →
  Term mid outs →
  Term ins mid →
  Term ins outs
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Split {ins outs : ℕ} (mid : ℕ) : Term ins outs → Set where
  _++'_ :
    (xs : Term mid outs)
    (ys : Term ins mid) →
    Split mid (xs ++ ys)

swap₁ : ∀ {ins mid outs} {xs ys : Term ins outs} →
  Split mid xs → Split mid ys → Term ins outs
swap₁ (xs ++' ys) (as ++' bs) = xs ++ bs

swap₂ : ∀ {ins mid outs} {xs ys : Term ins outs} →
  Split mid xs → Split mid ys → Term ins outs
swap₂ (xs ++' ys) (as ++' bs) = as ++ ys

swaps : ∀ {ins mid outs} {xs ys : Term ins outs} →
  Split mid xs → Split mid ys →
  Term ins outs × Term ins outs
swaps xs ys = swap₁ xs ys , swap₂ xs ys

split : ∀ {ins outs} (n : ℕ) (xs : Term ins outs) → ∃ λ mid → Split mid xs
split zero xs = _ , [] ++' xs
split (suc n) [] = _ , [] ++' []
split (suc n) (x ∷ xs) with split n xs
split (suc n) (x ∷ ._) | _ , xs ++' ys = _ , (x ∷ xs) ++' ys

splits : ∀ {ins outs} (n : ℕ) (mid : ℕ) → (xs : Term ins outs) → ∃ (Vec (Split mid xs))
splits zero mid xs with split zero xs
... | mid' , ys with mid ≟ mid'
... | yes p rewrite p = _ , ys ∷ []
... | no p = _ , []
splits (suc n) mid xs with split (suc n) xs
... | mid' , ys with mid ≟ mid' | splits n mid xs
... | yes p | _ , yss rewrite p = _ , ys ∷ yss
... | no p | _ , yss = _ , yss

length : ∀ {ins outs} → Term ins outs → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

split♀ : ∀ {ins outs} → (xs : Term ins outs) → Rand (∃ λ mid → Split mid xs)
split♀ xs = 
  rand >>= λ r →
  let i = r mod (suc (length xs))
  in return (split (toℕ i) xs)

split♂ : ∀ {ins outs} (xs : Term ins outs) (mid : ℕ) →
  Maybe (Rand (Split mid xs))
split♂ xs B
  with splits (length xs) B xs
... | zero , [] = nothing
... | suc n , xss = just (
  rand >>= λ r →
  return (lookup (r mod suc n) xss)
 )

crossover : ∀ {ins outs} (♀ ♂ : Term ins outs) →
  Rand (Term ins outs × Term ins outs)
crossover ♀ ♂ =
  split♀ ♀ >>= λ b,xs →
  maybe′
    (_=<<_ (return ∘ (swaps (proj₂ b,xs))))
    (return (♀ , ♂))
    (split♂ ♂ (proj₁ b,xs))

Population : (ins outs n : ℕ) → Set
Population ins outs n = Vec (Term ins outs) (2 + n)

module Initialization
  (match : (w : Word) (out : ℕ) → Dec (Σ ℕ λ n → out ≡ pre w n))
  where

  toMaybe : ∀ {w inp out} →
    Term inp out →
    Dec (∃ λ n → out ≡ pre w n) →
    Maybe (∃ λ n → Term inp n)
  toMaybe {w = w} ws (no _) = nothing
  toMaybe {w = w} ws (yes (_ , p))
    rewrite p = just (_ , w ∷ ws)

  enum-inp : (n inp : ℕ) → List Word → List (Σ ℕ λ out → Term inp out)
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

  init : (i inp out : ℕ) → List Word → List (Term inp out)
  init i inp out ws = filter-out out (enum-inp i inp ws)

module Evolution {ins outs : ℕ} (score : Term ins outs → ℕ) where

  _≥_ : ℕ → ℕ → Bool
  zero ≥ zero = true
  zero ≥ (suc n) = false
  (suc m) ≥ zero = true
  (suc m) ≥ (suc n) = m ≥ n

  select : ∀ {n} →
    Population ins outs n → Rand (Term ins outs)
  select {n = n} xss =
    rand >>= λ ii →
    rand >>= λ jj →
    let ♀ = lookup (ii mod (2 + n)) xss
        ♂ = lookup (jj mod (2 + n)) xss
    in return $
      if score ♀ ≥ score ♂
      then ♀ else ♂

  breed2 : ∀ {n} →
    Population ins outs n →
    Rand (Term ins outs × Term ins outs)
  breed2 xss =
    select xss >>= λ ♀ →
    select xss >>= λ ♂ →
    crossover ♀ ♂

  breedN : ∀ {m} → (n : ℕ) →
    Population ins outs m →
    Rand (Vec (Term ins outs) n)
  breedN zero xss = return []
  breedN (suc n) xss =
    breed2 xss >>= λ offspring →
    breedN n xss >>= λ ih →
    return (proj₁ offspring ∷ ih)

  evolve1 : ∀ {n} →
    Population ins outs n → Rand (Population ins outs n)
  evolve1 xss = breedN _ xss

  evolveN : ∀ {n} → (gens : ℕ) →
    Population ins outs n → Rand (Population ins outs n)
  evolveN zero xss = return xss
  evolveN (suc gens) xss =
    evolveN gens xss >>= evolve1

  evolve : ∀ {n} → (seed gens : ℕ) →
    Population ins outs n → Population ins outs n
  evolve seed gens xss =
    runRand (evolveN gens xss) seed

