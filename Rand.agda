module Rand where
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_)
open import Data.Product
open import State public

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


