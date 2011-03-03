module Stash.Rand where
open import Data.Nat
open import Relation.Nullary.Decidable
open import Data.Nat.DivMod renaming (_mod_ to _nmod_)
open import Data.Fin
open import Data.Product
open import Stash.State public

postulate Int : Set
{-# BUILTIN INTEGER Int #-}

primitive
  primIntegerPlus     : Int → Int → Int
  primIntegerMinus    : Int → Int → Int
  primIntegerTimes    : Int → Int → Int
  primIntegerDiv      : Int → Int → Int  -- partial
  primIntegerMod      : Int → Int → Int  -- partial
  primIntegerAbs      : Int → ℕ
  primNatToInteger    : ℕ → Int

multiplier : Int
multiplier = primNatToInteger 25173

incrementer : Int
incrementer = primNatToInteger 13849

modulus : Int
modulus = primNatToInteger 65536

nextRand : ℕ → ℕ
nextRand nat =
  let n = primNatToInteger nat
      product = primIntegerTimes n multiplier
      sum = primIntegerPlus product incrementer
      remainder = primIntegerMod sum modulus
  in primIntegerAbs remainder

calcRand : ℕ → ℕ × ℕ
calcRand n with nextRand n
... | next = next , next

rand : State ℕ ℕ
rand = state calcRand

Rand : Set → Set
Rand A = State ℕ A

runRand :  ∀ {A} → Rand A → ℕ → A
runRand st seed = proj₁ (runState st seed)

primNatMod : (dividend divisor : ℕ) → ℕ
primNatMod dividend zero = zero
primNatMod dividend (suc n) =
  let x = primNatToInteger dividend
      y = primNatToInteger (suc n)
      z = primIntegerMod x y
      nat = primIntegerAbs z
  in nat

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
_mod_ m n {p} = _nmod_ (primNatMod m n) n {p}
