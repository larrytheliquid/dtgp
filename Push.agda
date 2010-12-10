module Push where
open import Data.Bool
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; _≤_; _<_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality

delete : ∀ {A n} → Fin n → Vec A n → Vec A (Data.Nat.pred n)
delete zero (_ ∷ xs) = xs
delete (suc ()) (_ ∷ [])
delete (suc i) (x ∷ x' ∷ xs) = x ∷ delete i (x' ∷ xs)

yank : ∀ {A n} → Fin n → Vec A n → Vec A n
yank zero xs = lookup zero xs ∷ delete zero xs
yank (suc ()) (x ∷ [])
yank (suc i) (x ∷ x' ∷ xs) = lookup (suc i) (x ∷ x' ∷ xs) ∷ delete (suc i) (x ∷ x' ∷ xs)

data U : Set where
  EXEC BOOL NAT : U

data Inst : Set where
  ADD DIV : Inst
  NOT : Inst
  YANK : Inst

mutual
  Lit : U → Set
  Lit EXEC = Expr
  Lit BOOL = Bool
  Lit NAT = ℕ

  data Expr : Set where
    lit : {u : U} → Lit u → Expr
    inst : Inst → Expr

Stack : (u : U) → ℕ → Set
Stack u = Vec (Lit u)

data Intro : ∀ {x y z} → Stack EXEC x → Stack BOOL y → Stack NAT z → Set where
  EXEC : Intro [] [] []

  BOOL : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
           (b : Lit BOOL) →
           Intro es bs ns → Intro (lit b ∷ es) bs ns

data Elim : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z} →
            Intro es bs ns → Set where

  BOOL : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
         {b : Lit BOOL} →
         Prog (lit b ∷ es) bs ns → Prog es (b ∷ bs) ns

-- data Prog : ∀ {x y z} → Stack EXEC x → Stack BOOL y → Stack NAT z → Set where
--   I-EXEC : Prog [] [] []

--   I-BOOL : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--            (b : Lit BOOL) →
--            Prog es bs ns → Prog (lit b ∷ es) bs ns

--   E-BOOL : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--            {b : Lit BOOL} →
--            Prog (lit b ∷ es) bs ns → Prog es (b ∷ bs) ns

--   I-NAT : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           (n : Lit NAT) →
--           Prog es bs ns → Prog (lit n ∷ es) bs ns

--   E-NAT : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {n : Lit NAT} →
--           Prog (lit n ∷ es) bs ns → Prog es bs (n ∷ ns)

--   I-NOT : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {b : Lit BOOL} →
--           Prog es (b ∷ bs) ns → Prog (inst NOT ∷ es) (b ∷ bs) ns

--   E-NOT : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {b : Lit BOOL} →
--           Prog (inst NOT ∷ es) (b ∷ bs) ns → Prog es (not b ∷ bs) ns

--   I-ADD : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {n₁ n₂ : Lit NAT} →
--           Prog es bs (n₁ ∷ n₂ ∷ ns) → Prog (inst ADD ∷ es) bs (n₁ ∷ n₂ ∷ ns)

--   E-ADD : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {n₁ n₂ : Lit NAT} →
--           Prog (inst ADD ∷ es) bs (n₁ ∷ n₂ ∷ ns) → Prog es bs (n₂ + n₁ ∷ ns)

--   I-DIV : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {n₁ n₂ : Lit NAT} →
--           Prog es bs (suc n₁ ∷ n₂ ∷ ns) → Prog (inst DIV ∷ es) bs (suc n₁ ∷ n₂ ∷ ns)

--   E-DIV : ∀ {x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--           {n₁ n₂ : Lit NAT} →
--           Prog (inst DIV ∷ es) bs (suc n₁ ∷ n₂ ∷ ns) → Prog es bs (n₂ div suc n₁ ∷ ns)

--   I-YANK-BOOL :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < y) →
--     Prog es bs (n ∷ ns) → Prog (inst YANK ∷ es) bs (n ∷ ns)

--   E-YANK-BOOL :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < y) →
--     Prog (inst YANK ∷ es) bs (n ∷ ns) → Prog es (yank (fromℕ≤ pos) bs) ns

--   I-YANK-NAT :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < z) →
--     Prog es bs (n ∷ ns) → Prog (inst YANK ∷ es) bs (n ∷ ns)

--   E-YANK-NAT :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < z) →
--     Prog (inst YANK ∷ es) bs (n ∷ ns) → Prog es bs (yank (fromℕ≤ pos) ns)

--   I-YANK-EXEC :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < x) →
--     Prog es bs (n ∷ ns) → Prog (inst YANK ∷ es) bs (n ∷ ns)

--   E-YANK-EXEC :
--     ∀ {n x y z} {es : Stack EXEC x} {bs : Stack BOOL y} {ns : Stack NAT z}
--     (pos : n < x) →
--     Prog (inst YANK ∷ es) bs (n ∷ ns) → Prog (yank (fromℕ≤ pos) es) bs ns

-- div-not-args : Prog [] (true ∷ []) (2 ∷ 6 ∷ [])
-- div-not-args = E-NAT (E-BOOL (E-NAT (I-NAT 6 (I-BOOL true (I-NAT 2 I-EXEC)))))

-- div-not-call : Prog [] (false ∷ []) (3 ∷ [])
-- div-not-call = E-NOT (E-DIV (I-DIV (I-NOT div-not-args)))

-- yank-bool-args : Prog [] (true ∷ false ∷ []) (1 ∷ [])
-- yank-bool-args = E-BOOL (E-BOOL (E-NAT (I-NAT 1 (I-BOOL false (I-BOOL true I-EXEC)))))

-- yank-bool-call : Prog [] (false ∷ true ∷ []) []
-- yank-bool-call = E-YANK-BOOL (s≤s (s≤s z≤n)) (I-YANK-BOOL (s≤s (s≤s z≤n)) yank-bool-args)

-- yank-nat-args : Prog [] [] (1 ∷ 2 ∷ 3 ∷ [])
-- yank-nat-args = E-NAT (E-NAT (E-NAT (I-NAT 3 (I-NAT 2 (I-NAT 1 I-EXEC)))))

-- yank-nat-call : Prog [] [] (3 ∷ 2 ∷ [])
-- yank-nat-call = E-YANK-NAT (s≤s (s≤s z≤n)) (I-YANK-NAT (s≤s (s≤s z≤n)) yank-nat-args)

-- yank-exec-args : Prog (lit 2 ∷ lit 3 ∷ []) [] (1 ∷ [])
-- yank-exec-args = I-NAT 2 (I-NAT 3 (E-NAT (I-NAT 1 I-EXEC)))

-- yank-exec-call : Prog (lit 3 ∷ lit 2 ∷ []) [] []
-- yank-exec-call = E-YANK-EXEC (s≤s (s≤s z≤n)) (I-YANK-EXEC (s≤s (s≤s z≤n)) yank-exec-args)

-- yank-diverge-args : Prog (inst DIV ∷ lit 0 ∷ []) [] (1 ∷ 2 ∷ [])
-- yank-diverge-args = I-DIV (I-NAT 0 (E-NAT (E-NAT (I-NAT 2 (I-NAT 1 I-EXEC)))))

-- yank-diverge-control : Prog [] [] (0 ∷ 2 ∷ [])
-- yank-diverge-control = E-NAT (E-DIV yank-diverge-args)

-- yank-diverge-call : Prog (inst DIV ∷ []) [] (0 ∷ 2 ∷ [])
-- yank-diverge-call = E-NAT (E-YANK-EXEC (s≤s (s≤s z≤n)) (I-YANK-EXEC (s≤s (s≤s z≤n)) yank-diverge-args))

-- interleaved-diverge-args : Prog (lit 0 ∷ inst DIV ∷ []) [] (1 ∷ 2 ∷ [])
-- interleaved-diverge-args = I-NAT 0 (I-DIV (E-NAT (E-NAT (I-NAT 2 (I-NAT 1 I-EXEC)))))

-- interleaved-diverge-call : Prog (inst DIV ∷ []) [] (0 ∷ 1 ∷ 2 ∷ [])
-- interleaved-diverge-call = E-NAT interleaved-diverge-args

-- ordering1 : Prog [] [] (1 ∷ 2 ∷ [])
-- ordering1 = E-NAT (E-NAT (I-NAT 2 (I-NAT 1 I-EXEC)))

-- ordering2 : Prog [] [] (2 ∷ 1 ∷ [])
-- ordering2 = E-NAT (I-NAT 2 (E-NAT (I-NAT 1 I-EXEC)))
