-- The natural numbers.

{-# OPTIONS --without-K --safe #-}

module Tools.Nat where

open import Tools.PropositionalEquality
open import Tools.Nullary
open import Tools.Bool

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat using (_≤?_; _+_; _∸_) renaming (ℕ to Nat) public
open import Data.Nat.Show using (show) public

pattern 1+ n = suc n

-- Predecessor, cutting off at 0.

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- Decision of number equality.

infix 4 _≟_

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (subst (λ y → m ≡ pred y) x refl))
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

infix 4 _==_

_==_ : Nat → Nat → Bool
m == n with m ≟ n
... | yes _ = true
... | no _  = false



-- -- Max

-- max : (m n : Nat) → Nat
-- max zero k = k
-- max (suc m) zero = suc m
-- max (suc m) (suc n) = suc (max m n)

-- -- Less

-- data _≤_  : ∀ (n m : Nat) → Set where
--   ≤-0 : ∀ (m : Nat) → 0 ≤ m
--   ≤-s : ∀ {n m : Nat} → n ≤ m → suc n ≤ suc m

-- ≤-refl : ∀ (n : Nat) → n ≤ n
-- ≤-refl 0 = ≤-0 0
-- ≤-refl (suc n) = ≤-s (≤-refl n)

-- ≤-trans : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
-- ≤-trans {k = k} (≤-0 m) e = ≤-0 k
-- ≤-trans (≤-s e) (≤-s e') = ≤-s (≤-trans e e')


-- MaxLess-l : ∀ (n m : Nat) → n ≤ (max n m)
-- MaxLess-l zero k = ≤-0 k
-- MaxLess-l (suc n) zero = ≤-s (≤-refl n)
-- MaxLess-l (suc n) (suc m) = ≤-s (MaxLess-l n m)

-- MaxLess-r : ∀ (n m : Nat) → m ≤ (max n m)
-- MaxLess-r zero k = ≤-refl k
-- MaxLess-r (suc n) zero = ≤-0 _
-- MaxLess-r (suc n) (suc m) = ≤-s (MaxLess-r n m)

-- data _≤₃_ : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Set where
--   ≤₃-l : ∀ {a} b c {d} e f → a ≤ d → (a , b , c) ≤₃ (d , e , f)
--   ≤₃-m : ∀ a {b} c {d} e → b ≤ d → (a , b , c) ≤₃ (a , d , e)
--   ≤₃-r : ∀ a b {c} {d} → c ≤ d → (a , b , c) ≤₃ (a , b , d)

-- =-pred : ∀ {n m} → suc n ≡ suc m → n ≡ m
-- =-pred {n} {m} refl = refl
