module Wut where
module Check where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Stash
open import Utils

-- check : ∀ {m n} {t : Term (m + n)} → SplitAt m t → Typed t
-- check (xs ++' []) = {!!}
-- check (xs ++' y ∷ ys) with check (xs ++' ys)
-- ... | lolwut = {!!}

-- check : ∀ {m n} {t : Term (m + n)} → SplitAt m t → Typed t
-- check ([] ++' ys) = {!!}
-- check ((x ∷ xs) ++' ys) with check (xs ++' ys)
-- ... | lolwut = {!!}

-- check : ∀ {m n} {t : Term (m + n)} → SplitAt m t → Typed t
-- check ([] ++' ys) = {!!}
-- check ((w₃ ∷ w₂ ∷ w₁ ∷ []) ++' (Exec-S ∷ ys)) with check ((w₃ ∷ w₂ ∷ w₁ ∷ []) ++' ys)
-- ... | ohai = {!!}
-- check ((x ∷ xs) ++' []) = {!!}
-- check ((x ∷ xs) ++' (y ∷ ys)) with check (xs ++' ys)
-- ... | lolwut = {!!}

check : ∀ {m n} {t : Term (m + n)} → SplitAt m t → Typed t
check ([] ++' ys) = ill
check ((w₃ ∷ w₂ ∷ w₁ ∷ []) ++' (Exec-S ∷ ys)) with check ((w₃ ∷ w₂ ∷ w₁ ∷ []) ++' ys)
... | ohai = ill
check ((x ∷ xs) ++' []) = ill
check (xs ++' (Exec-STACKDEPTH ∷ ys)) with check (xs ++' ys)
... | well p = well (Exec-STACKDEPTH xs p)
... | ill = ill
check (xs ++' ys) = ill
