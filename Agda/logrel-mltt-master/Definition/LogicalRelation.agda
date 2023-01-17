{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed.Properties
open import Definition.Typed
open import Definition.Typed.Weakening

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Sum as TS

private
  variable
    ℓ : Nat
    Γ : Con Term ℓ
    l : LCon
    lε : ⊢ₗ l

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _/_⊩ne_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) : Set where
  constructor ne
  field
    K   : Term ℓ
    D   : Γ / lε ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ / lε ⊢ K ~ K ∷ U

-- Neutral type equality

data _/_⊩ne_≡_/_ (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) ([A] : Γ / lε ⊩ne A) → Set where
  ne₌ : ∀ {l} {lε : ⊢ₗ l} {A B} [A] (M   : Term ℓ) (D′  : Γ / lε ⊢ B :⇒*: M) (neM : Neutral M) (K≡M : Γ / lε ⊢ (_/_⊩ne_.K [A]) ~ M ∷ U)
        → Γ / lε ⊩ne A ≡ B / [A]
  ϝ⊩ne≡ : ∀ {l} {lε : ⊢ₗ l} {A B [A] m B' } mε {[A]t [A]f}
                     (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                     (αB : αNeutral {l} {lε} {_} m B')
                     → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ne A ≡ B / [A]t 
                     → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ne A ≡ B / [A]f
                     → Γ / lε ⊩ne A ≡ B / [A]
                     
-- record _/_⊩ne_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
--   constructor ne₌
--   open _/_⊩ne_ [A]
--   field
--     M   : Term ℓ
--     D′  : Γ / lε ⊢ B :⇒*: M
--     neM : Neutral M
--     K≡M : Γ / lε ⊢ K ~ M ∷ U  
  
-- record _/_⊩neNf_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k A : Term ℓ) : Set where
--   inductive
--   constructor neNfₜ
--   field
--     neK  : Neutral k
--     ⊢k   : Γ / lε ⊢ k ∷ A
--     k≡k  : Γ / lε ⊢ k ~ k ∷ A

mutual 
-- Neutral term in WHNF
  data _/_⊩neNf_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k A : Term ℓ) : Set where
    neNfₜ : ∀ (neK  : Neutral k) (⊢k   : Γ / lε ⊢ k ∷ A)
              (k≡k  : Γ / lε ⊢ k ~ k ∷ A)
              → Γ / lε ⊩neNf k ∷ A
    neNfϝ : ∀ {m mε [A]t [A]f}
                    → Γ / lε ⊢ k ∷ A
                    → αNeutral {l} {lε} m k
                    → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ne k ∷ A / [A]t
                    → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ne k ∷ A / [A]f
                    → Γ / lε ⊩neNf k ∷ A
                       
-- Neutral term
  record _/_⊩ne_∷_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
    inductive
    constructor neₜ
    open _/_⊩ne_ [A]
    field
      k   : Term ℓ
      d   : Γ / lε ⊢ t :⇒*: k ∷ K
      nf  : Γ / lε ⊩neNf k ∷ K


-- record _/_⊩neNf_≡_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k m A : Term ℓ) : Set where
--   inductive
--   constructor neNfₜ₌
--   field
--     neK  : Neutral k
--     neM  : Neutral m
--     k≡m  : Γ / lε ⊢ k ~ m ∷ A


mutual
-- Neutral term equality in WHNF
  data _/_⊩neNf_≡_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k k' A : Term ℓ) : Set where
    neNfₜ₌ : ∀ (neK  : Neutral k) (neK'  : Neutral k') (k≡m  : Γ / lε ⊢ k ~ k' ∷ A)
           → Γ / lε ⊩neNf k ≡ k' ∷ A
    ⊩neNfϝ-l : ∀ {m mε [A]t [A]f} → αNeutral {l} {lε} m k
                                  → Γ / lε ⊩neNf k' ∷ A
                                  → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ne k ≡ k' ∷ A / [A]t
                                  → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ne k ≡ k' ∷ A / [A]f
                                  → Γ / lε ⊩neNf k ≡ k' ∷ A
    ⊩neNfϝ-r : ∀ {m mε [A]t [A]f} → Γ / lε ⊩neNf k ∷ A
                                  → αNeutral {l} {lε} m k'
                                  → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ne k ≡ k' ∷ A / [A]t
                                  → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ne k ≡ k' ∷ A / [A]f
                                  → Γ / lε ⊩neNf k ≡ k' ∷ A

-- Neutral term equality
  record _/_⊩ne_≡_∷_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
    inductive
    constructor neₜ₌
    open _/_⊩ne_ [A]
    field
      k m : Term ℓ
      d   : Γ / lε ⊢ t :⇒*: k ∷ K
      d′  : Γ / lε ⊢ u :⇒*: m ∷ K
      nf  : Γ / lε ⊩neNf k ≡ m ∷ K
    
-- Reducibility of αNeutrals:

-- αNeutral type
-- record _/_⊩αne_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) : Set where
--  constructor αne
--  field
--    K   : Term ℓ
--    D   : Γ / lε ⊢ A :⇒*: K
--    neK : αNeutral {l} {lε} K
--    K≡K : Γ / lε ⊢ K ≅ K ∷ U

-- αNeutral type equality
-- record _/_⊩αne_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) ([A] : Γ / lε ⊩αne A) : Set where
--  constructor αne₌
--  open _/_⊩αne_ [A]
--  field
--    M   : Term ℓ
--    D′  : Γ / lε ⊢ B :⇒*: M
--    K≡M : Γ / lε ⊢ K ≅ M ∷ U

-- Reducibility of natural numbers:

-- Natural number type
_/_⊩ℕ_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩ℕ A = Γ / lε ⊢ A :⇒*: ℕ

-- Natural number type equality
data _/_⊩ℕ_≡_ (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
  where 
    ⊩ℕ≡ : ∀ {l} {lε : ⊢ₗ l} A B → Γ / lε ⊢ B ⇒* ℕ → Γ / lε ⊩ℕ A ≡ B
    ϝ⊩ℕ≡ : ∀ {l} {lε : ⊢ₗ l} {m A B B'} mε
                       (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                       (αB : αNeutral {l} {lε} {_} m B')
                       → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ℕ A ≡ B 
                       → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ℕ A ≡ B 
                       → Γ / lε ⊩ℕ A ≡ B

mutual
  -- Natural number term
  record _/_⊩ℕ_∷ℕ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
    inductive
    constructor ℕₜ
    field
      n : Term ℓ
      d : Γ / lε ⊢ t :⇒*: n ∷ ℕ
      n≡n : Γ / lε ⊢ n ≅ n ∷ ℕ
      prop : Natural-prop Γ lε n

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n : Term ℓ) → Set where
    sucᵣ  : ∀ {n} → Γ / lε ⊩ℕ n ∷ℕ → Natural-prop Γ lε (suc n)
    zeroᵣ : Natural-prop Γ lε zero
    ne    : ∀ {n} → Γ / lε ⊩neNf n ∷ ℕ → Natural-prop Γ lε n
    ℕϝ    : ∀ {n m mε} → Γ / lε ⊢ n ∷ ℕ
                       → αNeutral {l} {lε} m n
                       → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ℕ n ∷ℕ
                       → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ℕ n ∷ℕ
                       → Natural-prop Γ lε n

mutual
  -- Natural number term equality
  record _/_⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
    inductive
    constructor ℕₜ₌
    field
      k k′ : Term ℓ
      d : Γ / lε ⊢ t :⇒*: k  ∷ ℕ
      d′ : Γ / lε ⊢ u :⇒*: k′ ∷ ℕ
      k≡k′ : Γ / lε ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ lε k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (n n′ : Term ℓ) → Set where
    sucᵣ  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ lε (suc n) (suc n′)
    zeroᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Natural]-prop Γ lε zero zero
    ne    : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ lε n n′
    [ℕ]ϝ-l  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n' m mε}  → αNeutral {l} {lε} m n
                                                    → Natural-prop Γ lε n'
                                                   → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ℕ n ≡ n' ∷ℕ
                                                   → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ℕ n ≡ n' ∷ℕ
                                                   → [Natural]-prop Γ lε n n'
    [ℕ]ϝ-r  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n' m mε} → Natural-prop Γ lε n
                                                   → αNeutral {l} {lε} m n'
                                                   → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩ℕ n ≡ n' ∷ℕ
                                                   → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩ℕ n ≡ n' ∷ℕ
                                                   → [Natural]-prop Γ lε n n'

-- Natural extraction from term WHNF property
natural : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Natural-prop Γ lε n → Natural {_} {l} {lε} n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK
natural (ne (neNfϝ x αn x₂ x₃)) = neα αn
natural (ℕϝ ⊢n αn nt nf) = neα αn

-- Natural extraction from term equality WHNF property
split : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Natural]-prop Γ lε a b → Natural {_} {l} {lε} a × Natural {_} {l} {lε} b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM
split (ne (⊩neNfϝ-l αk nek' x₂ x₃)) = neα αk , natural (ne nek')
split (ne (⊩neNfϝ-r nek αk' x₂ x₃)) = natural (ne nek) , neα αk'
split ([ℕ]ϝ-l αn [n'] tn=n' fn=n') = neα αn , natural [n']
split ([ℕ]ϝ-r [n] αn' tn=n' fn=n') = natural [n] , neα αn'

-- Boolean type
_/_⊩𝔹_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩𝔹 A = Γ / lε ⊢ A :⇒*: 𝔹
-- Boolean type equality
data _/_⊩𝔹_≡_ (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
  where 
    ⊩𝔹≡ : ∀ {l} {lε : ⊢ₗ l} A B → Γ / lε ⊢ B ⇒* 𝔹 → Γ / lε ⊩𝔹 A ≡ B
    ϝ⊩𝔹≡ : ∀ {l} {lε : ⊢ₗ l} {m A B B'} mε
                       (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                       (αB : αNeutral {l} {lε} {_} m B')
                       → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩𝔹 A ≡ B 
                       → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩𝔹 A ≡ B 
                       → Γ / lε ⊩𝔹 A ≡ B

mutual
  -- Boolean term
  record _/_⊩𝔹_∷𝔹 (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
    inductive
    constructor 𝔹ₜ
    field
      b : Term ℓ
      d : Γ / lε ⊢ t :⇒*: b ∷ 𝔹
      n≡n : Γ / lε ⊢ b ≅ b ∷ 𝔹
      prop : Boolean-prop Γ lε b

  -- WHNF property of boolean terms
  data Boolean-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (b : Term ℓ) → Set where
    trueᵣ : Boolean-prop Γ lε true
    falseᵣ : Boolean-prop Γ lε false
    ne    : ∀ {b} → Γ / lε ⊩neNf b ∷ 𝔹 → Boolean-prop Γ lε b
    𝔹ϝ    : ∀ {b m mε} → Γ / lε ⊢ b ∷ 𝔹
                       → αNeutral {l} {lε} m b
                       → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩𝔹 b ∷𝔹
                       → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩𝔹 b ∷𝔹
                       → Boolean-prop Γ lε b

mutual
  -- Natural number term equality
  record _/_⊩𝔹_≡_∷𝔹 (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
    inductive
    constructor 𝔹ₜ₌
    field
      b b′ : Term ℓ
      d : Γ / lε ⊢ t :⇒*: b ∷ 𝔹
      d′ : Γ / lε ⊢ u :⇒*: b′ ∷ 𝔹
      b≡b′ : Γ / lε ⊢ b ≅ b′ ∷ 𝔹
      prop : [Boolean]-prop Γ lε b b′

  -- WHNF property of Natural number term equality
  data [Boolean]-prop (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (n n′ : Term ℓ) → Set where
    trueᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Boolean]-prop Γ lε true true
    falseᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Boolean]-prop Γ lε false false
    ne    : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ 𝔹 → [Boolean]-prop Γ lε n n′
    [𝔹]ϝ-l  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n' m mε}   → αNeutral {l} {lε} m n
                                                    → Boolean-prop Γ lε n'
                                                    → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩𝔹 n ≡ n' ∷𝔹
                                                    → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩𝔹 n ≡ n' ∷𝔹
                                                    → [Boolean]-prop Γ lε n n'
    [𝔹]ϝ-r  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n' m mε}  → Boolean-prop Γ lε n
                                                   → αNeutral {l} {lε} m n'
                                                   → Γ / (⊢ₗ• l lε m Btrue mε)  ⊩𝔹 n ≡ n' ∷𝔹
                                                   → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩𝔹 n ≡ n' ∷𝔹
                                                   → [Boolean]-prop Γ lε n n'

-- Boolean extraction from term WHNF property
boolean : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Boolean-prop Γ lε n → Boolean {_} {l} {lε} n
boolean trueᵣ = trueₙ
boolean falseᵣ = falseₙ
boolean (ne (neNfₜ neK ⊢k k≡k)) = ne neK
boolean (ne (neNfϝ x αn x₂ x₃)) = neα αn
boolean (𝔹ϝ ⊢n αn nt nf) = neα αn

-- Boolean from term equality WHNF property
bsplit : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Boolean]-prop Γ lε a b → Boolean {_} {l} {lε} a × Boolean {_} {l} {lε} b
bsplit trueᵣ = trueₙ , trueₙ
bsplit falseᵣ = falseₙ , falseₙ
bsplit (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM
bsplit (ne (⊩neNfϝ-l αk nek' x₂ x₃)) = neα αk , boolean (ne nek')
bsplit (ne (⊩neNfϝ-r nek αk' x₂ x₃)) = boolean (ne nek) , neα αk'
bsplit ([𝔹]ϝ-l αn [n'] tn=n' fn=n') = neα αn , boolean [n']
bsplit ([𝔹]ϝ-r [n] αn' tn=n' fn=n') = boolean [n] , neα αn'


-- -- Reducibility of Empty

-- -- Empty type
-- _/_⊩Empty_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
-- Γ / lε ⊩Empty A = Γ / lε ⊢ A :⇒*: Empty

-- -- Empty type equality
-- _/_⊩Empty_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
-- Γ / lε ⊩Empty A ≡ B = Γ / lε ⊢ B ⇒* Empty

-- -- WHNF property of absurd terms
-- data Empty-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n : Term ℓ) → Set where
--   ne    : ∀ {n} → Γ / lε ⊩neNf n ∷ Empty → Empty-prop Γ lε n

-- -- Empty term
-- record _/_⊩Empty_∷Empty (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
--   inductive
--   constructor Emptyₜ
--   field
--     n : Term ℓ
--     d : Γ / lε ⊢ t :⇒*: n ∷ Empty
--     n≡n : Γ / lε ⊢ n ≅ n ∷ Empty
--     prop : Empty-prop Γ lε n

-- data [Empty]-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n n′ : Term ℓ) → Set where
--   ne    : ∀ {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ lε n n′

-- -- Empty term equality
-- record _/_⊩Empty_≡_∷Empty (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
--   inductive
--   constructor Emptyₜ₌
--   field
--     k k′ : Term ℓ
--     d : Γ / lε ⊢ t :⇒*: k  ∷ Empty
--     d′ : Γ / lε ⊢ u :⇒*: k′ ∷ Empty
--     k≡k′ : Γ / lε ⊢ k ≅ k′ ∷ Empty
--     prop : [Empty]-prop Γ lε k k′

-- empty : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Empty-prop Γ lε n → Neutral n
-- empty (ne (neNfₜ neK _ _)) = neK

-- esplit : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Empty]-prop Γ lε a b → Neutral a × Neutral b
-- esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- -- Reducibility of Unit

-- -- Unit type
-- _/_⊩Unit_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
-- Γ / lε ⊩Unit A = Γ / lε ⊢ A :⇒*: Unit

-- -- Unit type equality
-- _/_⊩Unit_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
-- Γ / lε ⊩Unit A ≡ B = Γ / lε ⊢ B ⇒* Unit

-- record _/_⊩Unit_∷Unit (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
--   inductive
--   constructor Unitₜ
--   field
--     n : Term ℓ
--     d : Γ / lε ⊢ t :⇒*: n ∷ Unit
--     prop : Whnf {l} {lε} n

-- -- Unit term equality
-- record _/_⊩Unit_≡_∷Unit (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
--   constructor Unitₜ₌
--   field
--     ⊢t : Γ / lε ⊢ t ∷ Unit
--     ⊢u : Γ / lε ⊢ u ∷ Unit

-- -- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Logical relation
-- Exported interface
record LogRelKit : Set₁ where
  constructor Kit
  field
    _/_⊩U : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) → Set
    _/_⊩B⟨_⟩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) → Term ℓ → Set

    _/_⊩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) → Term ℓ → Set
    _/_⊩_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩ A → Set
    _/_⊩_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩ A → Set
    _/_⊩_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩ A → Set

module LogRel (j : TypeLevel) (rec : ∀ {j′} → j′ < j → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _/_⊩¹U (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : Set where
    constructor Uᵣ
    field
      j′ : TypeLevel
      j< : j′ < j
      ⊢Γ : ⊢ Γ / lε

  -- Universe type equality
  _/_⊩¹U≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (B : Term ℓ) → Set
  Γ / lε ⊩¹U≡ B = B PE.≡ U -- Note lack of reduction

  -- Universe term
  record _/_⊩¹U_∷U/_ {j′} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) (j< : j′ < j) : Set where
    constructor Uₜ
    open LogRelKit (rec j<)
    field
      A     : Term ℓ
      d     : Γ / lε ⊢ t :⇒*: A ∷ U
      typeA : Type {_} {l} {lε} A
      A≡A   : Γ / lε ⊢ A ≅ A ∷ U
      [t]   : Γ / lε ⊩ t

  -- Universe term equality
  record _/_⊩¹U_≡_∷U/_ {j′} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) (j< : j′ < j) : Set where
    constructor Uₜ₌
    open LogRelKit (rec j<)
    field
      A B   : Term ℓ
      d     : Γ / lε ⊢ t :⇒*: A ∷ U
      d′    : Γ / lε ⊢ u :⇒*: B ∷ U
      typeA : Type {_} {l} {lε} A
      typeB : Type {_} {l} {lε} B
      A≡B   : Γ / lε ⊢ A ≅ B ∷ U
      [t]   : Γ / lε ⊩ t
      [u]   : Γ / lε ⊩ u
      [t≡u] : Γ / lε ⊩ t ≡ u / [t]

  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _/_⊩¹B⟨_⟩_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) (A : Term ℓ) : Set where
      inductive
      constructor Bᵣ
      eta-equality
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ / lε ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
        ⊢F : Γ / lε ⊢ F
        ⊢G : Γ ∙ F / lε ⊢ G
        A≡A : Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {l' : LCon} {≤ε : l  ≤ₗ l'} {lε' : ⊢ₗ l'} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ / lε' → Δ / lε' ⊩¹ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
            → Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ
            → Δ / lε' ⊩¹ U.wk (lift ρ) G [ a ]
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
              → ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
              → ([b] : Δ / lε' ⊩¹ b ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
              → Δ / lε' ⊩¹ a ≡ b ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ      
              → Δ / lε' ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]
      

    -- B-type equality
    data _/_⊩¹B⟨_⟩_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) (A B : Term ℓ) : ∀ ([A] : Γ / lε ⊩¹B⟨ W ⟩ A) → Set
      where
        B₌ : ∀  (F : Term ℓ)
                (G : Term (1+ ℓ))
                (D : Γ / lε ⊢ A :⇒*: ⟦ W ⟧ F ▹ G)
                (⊢F : Γ / lε ⊢ F)
                (⊢G : Γ ∙ F / lε ⊢ G)
                (A≡A : Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G)
                ([F] : ∀ {m} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ / lε' → Δ / lε' ⊩¹ U.wk ρ F)
                ([G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
                  → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
                  → Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ
                  → Δ / lε' ⊩¹ U.wk (lift ρ) G [ a ])
                (G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
                         → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
                         → ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                         → ([b] : Δ / lε' ⊩¹ b ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                         → Δ / lε' ⊩¹ a ≡ b ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ
                         → Δ / lε' ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a])
                (F′ : Term ℓ)
                (G′     : Term (1+ ℓ))
                (D′     : Γ / lε ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′)
                (A≡B    : Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′)
                ([F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}  {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
                       → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
                       → Δ / lε' ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                ([G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}  {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
                         → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
                         → ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                         → Δ / lε' ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a])
                → Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / (Bᵣ F G D ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} {lε'} → [F] {m} {l'} {≤ε} {lε'}) [G] (G-ext))
        Bϝ : ∀ {m mε B'} ([A] : Γ / lε ⊩¹B⟨ W ⟩ A)
                         (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                         (αB : αNeutral {l} {lε} {_} m B')
                         [A]t [A]f
                     →  Γ / (⊢ₗ• l lε m Btrue mε)  ⊩¹B⟨ W ⟩ A ≡ B / [A]t
                     →  Γ / (⊢ₗ• l lε m Bfalse mε) ⊩¹B⟨ W ⟩ A ≡ B / [A]f
                     →  Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / [A]

    -- Term reducibility of Π-type
    _/_⊩¹Π_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_∷_/_ {ℓ} Γ {l} lε t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ f → Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G
            × Function {_} {_} {lε} f
            × Γ / lε ⊢ f ≅ f ∷ Π F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
              ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
              ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} {lε'} [ρ] ⊢Δ)
              ([b] : Δ / lε' ⊩¹ b ∷ U.wk ρ F / [F]  {_} {l'} {≤ε} {lε'} [ρ] ⊢Δ)
              ([a≡b] : Δ / lε' ⊩¹ a ≡ b ∷ U.wk ρ F / [F]  {_} {l'} {≤ε} {lε'} [ρ] ⊢Δ)
              → Δ / lε' ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
              → ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} {lε'} [ρ] ⊢Δ)
              → Δ / lε' ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _/_⊩¹Π_≡_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_≡_∷_/_  {ℓ} Γ {l} lε t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ f g → Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G
               × Γ / lε ⊢ u :⇒*: g ∷ Π F ▹ G
               × Function {_} {_} {lε} f
               × Function {_} {_} {lε} g
               × Γ / lε ⊢ f ≅ g ∷ Π F ▹ G
               × Γ / lε ⊩¹Π t ∷ A / [A]
               × Γ / lε ⊩¹Π u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} {l' : LCon} {≤ε : l ≤ₗ l'} {lε' : ⊢ₗ l'}
                 ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
                 ([a] : Δ / lε' ⊩¹ a ∷ U.wk ρ F / [F] {_} {l'} {≤ε} {lε'} [ρ] ⊢Δ)
                 → Δ / lε' ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _/_⊩¹Σ_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΣ ⟩ A) → Set
    Γ / lε ⊩¹Σ t ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ p → Γ / lε ⊢ t :⇒*: p ∷ Σ F ▹ G
            × Product p
            × Γ / lε ⊢ p ≅ p ∷ Σ F ▹ G
            × (Σ (Γ / lε ⊩¹ fst p ∷ U.wk id F / [F] {_} {_} {λ n l inl → inl} {lε} id (wf ⊢F)) λ [fst]
                 → Γ / lε ⊩¹ snd p ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fst])

    -- Term equality of Σ-type
    _/_⊩¹Σ_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΣ ⟩ A) → Set
    Γ / lε ⊩¹Σ t ≡ u ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ p r → Γ / lε ⊢ t :⇒*: p ∷ Σ F ▹ G
               × Γ / lε ⊢ u :⇒*: r ∷ Σ F ▹ G
               × Product p
               × Product r
               × Γ / lε ⊢ p ≅ r ∷ Σ F ▹ G
               × Γ / lε ⊩¹Σ t ∷ A / [A]
               × Γ / lε ⊩¹Σ u ∷ A / [A]
               × (Σ (Γ / lε ⊩¹ fst p ∷ U.wk id F / [F] {_} {_} {λ n l inl → inl} {lε} id (wf ⊢F)) λ [fstp]
                    → Γ / lε ⊩¹ fst r ∷ U.wk id F / [F] {_} {_} {λ n b inl → inl} {lε} id (wf ⊢F)
                    × Γ / lε ⊩¹ fst p ≡ fst r ∷ U.wk id F / [F] {_} {_} {λ n b inl → inl} {lε} id (wf ⊢F)
                    × Γ / lε ⊩¹ snd p ≡ snd r ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fstp])

    -- Logical relation definition
    data _/_⊩¹_ (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) → Term ℓ → Set where
      Uᵣ  : Γ / lε ⊩¹U → Γ / lε ⊩¹ U
      ℕᵣ  : ∀ {A} → Γ / lε ⊩ℕ A → Γ / lε ⊩¹ A
      𝔹ᵣ : ∀ {A} → Γ / lε ⊩𝔹 A → Γ / lε ⊩¹ A
--      Emptyᵣ : ∀ {A} → Γ / lε ⊩Empty A → Γ / lε ⊩¹ A
--      Unitᵣ : ∀ {A} → Γ / lε ⊩Unit A → Γ / lε ⊩¹ A
      ne  : ∀ {A} → Γ / lε ⊩ne A → Γ / lε ⊩¹ A
      Bᵣ  : ∀ {A} W → Γ / lε ⊩¹B⟨ W ⟩ A → Γ / lε ⊩¹ A
      emb : ∀ {A j′} (j< : j′ < j) (let open LogRelKit (rec j<))
            ([A] : Γ / lε ⊩ A) → Γ / lε ⊩¹ A
      ϝᵣ  : ∀ {A B m} mε   → Γ / lε ⊢ A :⇒*: B
                           → αNeutral {l} {lε} m B
                           → Γ / (⊢ₗ• l lε m Btrue mε)     ⊩¹ A
                           → Γ / (⊢ₗ• l lε m Bfalse mε)    ⊩¹ A
                           → Γ / lε ⊩¹ A

    _/_⊩¹_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ A ≡ B / Uᵣ UA = Γ / lε ⊩¹U≡ B
    Γ / lε ⊩¹ A ≡ B / ℕᵣ D = Γ / lε ⊩ℕ A ≡ B
    Γ / lε ⊩¹ A ≡ B / 𝔹ᵣ D = Γ / lε ⊩𝔹 A ≡ B
--    Γ / lε ⊩¹ A ≡ B / Emptyᵣ D = Γ / lε ⊩Empty A ≡ B
--    Γ / lε ⊩¹ A ≡ B / Unitᵣ D = Γ / lε ⊩Unit A ≡ B
    Γ / lε ⊩¹ A ≡ B / ne neA = Γ / lε ⊩ne A ≡ B / neA
    Γ / lε ⊩¹ A ≡ B / Bᵣ W BA = Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / BA
    Γ / lε ⊩¹ A ≡ B / ϝᵣ _ _ _ tB fB = (Γ / _ ⊩¹ _ ≡ B / tB) × (Γ / _ ⊩¹ _ ≡ B / fB)
    Γ / lε ⊩¹ A ≡ B / emb j< [A] = Γ / lε ⊩ A ≡ B / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ t ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / lε ⊩¹U t ∷U/ j<
    Γ / lε ⊩¹ t ∷ A / ℕᵣ D = Γ / lε ⊩ℕ t ∷ℕ
    Γ / lε ⊩¹ t ∷ A / 𝔹ᵣ D = Γ / lε ⊩𝔹 t ∷𝔹    
--    Γ / lε ⊩¹ t ∷ A / Emptyᵣ D = Γ / lε ⊩Empty t ∷Empty
--    Γ / lε ⊩¹ t ∷ A / Unitᵣ D = Γ / lε ⊩Unit t ∷Unit
    Γ / lε ⊩¹ t ∷ A / ne neA = Γ / lε ⊩ne t ∷ A / neA
    Γ / lε ⊩¹ t ∷ A / Bᵣ BΠ ΠA  = Γ / lε ⊩¹Π t ∷ A / ΠA
    Γ / lε ⊩¹ t ∷ A / Bᵣ BΣ ΣA  = Γ / lε ⊩¹Σ t ∷ A / ΣA
    Γ / lε ⊩¹ t ∷ A / ϝᵣ _ _ _ tB fB = (Γ / _ ⊩¹ t ∷ _ / tB) × (Γ / _ ⊩¹ t ∷ _ / fB)
    Γ / lε ⊩¹ t ∷ A / emb j< [A] = Γ / lε ⊩ t ∷ A / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ t ≡ u ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / lε ⊩¹U t ≡ u ∷U/ j<
    Γ / lε ⊩¹ t ≡ u ∷ A / ℕᵣ D = Γ / lε ⊩ℕ t ≡ u ∷ℕ
    Γ / lε ⊩¹ t ≡ u ∷ A / 𝔹ᵣ D = Γ / lε ⊩𝔹 t ≡ u ∷𝔹
--    Γ / lε ⊩¹ t ≡ u ∷ A / Emptyᵣ D = Γ / lε ⊩Empty t ≡ u ∷Empty
--    Γ / lε ⊩¹ t ≡ u ∷ A / Unitᵣ D = Γ / lε ⊩Unit t ≡ u ∷Unit
    Γ / lε ⊩¹ t ≡ u ∷ A / ne neA = Γ / lε ⊩ne t ≡ u ∷ A / neA
    Γ / lε ⊩¹ t ≡ u ∷ A / Bᵣ BΠ ΠA = Γ / lε ⊩¹Π t ≡ u ∷ A / ΠA
    Γ / lε ⊩¹ t ≡ u ∷ A / Bᵣ BΣ ΣA  = Γ / lε ⊩¹Σ t ≡ u ∷ A / ΣA
    Γ / lε ⊩¹ t ≡ u ∷ A / ϝᵣ _ _ _ tB fB = (Γ / _ ⊩¹ t ≡ u ∷ _ / tB) × (Γ / _ ⊩¹ t ≡ u ∷ _ / fB)
    Γ / lε ⊩¹ t ≡ u ∷ A / emb j< [A] = Γ / lε ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec j<)

    kit : LogRelKit
    kit = Kit _/_⊩¹U _/_⊩¹B⟨_⟩_
              _/_⊩¹_ _/_⊩¹_≡_/_ _/_⊩¹_∷_/_ _/_⊩¹_≡_∷_/_

  ⊩¹B≤ : ∀ Γ W {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A : Term ℓ}
             → l ≤ₗ l'
             → Γ / lε ⊩¹B⟨ W ⟩ A
             → Γ / lε' ⊩¹B⟨ W ⟩ A
  ⊩¹B≤ Γ W f< (Bᵣ F G [ ⊢A , ⊢B , d ] ⊢F ⊢G A≡A [F] [G] G-ext) =
   Bᵣ F G [ Ty≤ f< ⊢A , Ty≤ f< ⊢B , Red≤* f< d ] (Ty≤ f< ⊢F) (Ty≤ f< ⊢G) (≅-≤ f< A≡A) (λ {m} {l'} {≤ε} → [F] {_} {_} { λ _ _ nε → ≤ε _ _ (f< _ _ nε) }) [G] G-ext

  τ⊩¹B : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) {n} {b} nε (W : BindingType) (A : Term ℓ) → Γ / lε ⊩¹B⟨ W ⟩ A → Γ / (⊢ₗ• l lε n b nε) ⊩¹B⟨ W ⟩ A
  τ⊩¹B Γ lε {n} {b} nε w A (Bᵣ F G [ ⊢A , ⊢B , d ] ⊢F ⊢G A≡A [F] [G] G-ext) =
      Bᵣ F G [ τTy lε n b nε ⊢A , τTy _ _ _ nε ⊢B , τRed* d ] (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) (λ {m} {l'} {≤ε} → [F] {_} {_} {≤ₗ-rev ≤ε}) [G] G-ext
         
  AntiRedConvW : ∀ {A B C} W ([C] : Γ / lε ⊩¹B⟨ W ⟩ C) (C≡B :  Γ / lε ⊩¹B⟨ W ⟩ C ≡ B / [C]) →  Γ / lε ⊢ A :⇒*: B
               →  Γ / lε  ⊩¹B⟨ W ⟩ C ≡ A / [C]
  AntiRedConvW W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' B≡C [F≡F'] [G≡G']) A⇒B =
    B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (⇒*-comp (red A⇒B) D') B≡C [F≡F'] [G≡G']
  AntiRedConvW W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ [C] B⇒B' αB' [C]t [C]f tB≡C fB≡C) A⇒B =
    Bϝ [C] (:⇒:*-comp A⇒B B⇒B') αB' [C]t [C]f (AntiRedConvW W [C]t tB≡C (τwfRed* A⇒B)) (AntiRedConvW W [C]f fB≡C (τwfRed* A⇒B))
    

  RedConvW-r : ∀ {A B C} W ([C] : Γ / lε ⊩¹B⟨ W ⟩ C) (C≡A :  Γ / lε ⊩¹B⟨ W ⟩ C ≡ A / [C]) →  Γ / lε ⊢ A :⇒*: B
               →  Γ / lε  ⊩¹B⟨ W ⟩ C ≡ B / [C]
  RedConvW-r W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' B≡C [F≡F'] [G≡G']) A⇒B =
    B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (whrDet↘ (D' , ⟦ W ⟧ₙ) (red A⇒B)) B≡C [F≡F'] [G≡G']
  RedConvW-r W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ [C] A⇒B' αB' [C]t [C]f tB≡C fB≡C) A⇒B =
    Bϝ [C] ([ ⊢B-red A⇒B , ⊢B-red A⇒B' , whrDet↘ (red A⇒B' , αₙ αB') (red A⇒B) ]) αB' [C]t [C]f
       (RedConvW-r W [C]t tB≡C (τwfRed* A⇒B))
       (RedConvW-r W [C]f fB≡C (τwfRed* A⇒B))

  RedW : ∀ {A B} W ([A] : Γ / lε ⊩¹B⟨ W ⟩ A) → Γ / lε ⊢ A :⇒*: B → Γ / lε ⊩¹B⟨ W ⟩ B
  RedW W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒B =
    Bᵣ F G ([ ⊢B-red A⇒B , ⊢B-red D , whrDet↘ (red D , ⟦ W ⟧ₙ) (red A⇒B) ]) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {_} {_} {≤ε}) [G] G-ext
                                                                                                                           
  RedConvW-l : ∀ {W A A' B} ([A] : Γ / lε ⊩¹B⟨ W ⟩ A)
                      → (A⇒A' : Γ / lε ⊢ A :⇒*: A')
                      → Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / [A]
                      → Γ / lε ⊩¹B⟨ W ⟩ A' ≡ B / RedW W [A] A⇒A'
  RedConvW-l  {W = W} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'
    (B₌ _ _ _ _ _ _ _ _ _ F2 G2 D2 A≡B [F=F2] [G=G2])  = B₌ _ _ _ _ _ _ _ _ _ F2 G2 D2 A≡B [F=F2] [G=G2]
  RedConvW-l  {W = W} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'
    (Bϝ _ B⇒B' αB' [A]t [A]f tA≡B fA≡B) = Bϝ _ B⇒B' αB' (RedW W [A]t (τwfRed* A⇒A')) (RedW W [A]f (τwfRed* A⇒A'))
          (RedConvW-l [A]t (τwfRed* A⇒A') tA≡B)
            (RedConvW-l [A]f (τwfRed* A⇒A') fA≡B)
    

  whescapeEqB : ∀ {W A B} (whA : Whnf {l} {lε} A) → ([A] : Γ / lε  ⊩¹B⟨ W ⟩ A)
              → Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / [A]
             → Γ / lε ⊢ A ≅ B
  whescapeEqB {W = W} whA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' A≡B [F=F'] [G=G']) =
    ≅-red (red D) D' ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
  whescapeEqB {W = W} whA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ _ B⇒B' αB' [A]t [A]f tA≡B fA≡B)
    rewrite whrDet* (red D , ⟦ W ⟧ₙ) (id (⊢A-red D) , whA) =
   ≅-ϝ (whescapeEqB (PE.subst (λ K → Whnf K) (whrDet* (red D , ⟦ W ⟧ₙ) (id (⊢A-red D) , whA)) ⟦ W ⟧ₙ) [A]t tA≡B)
       (whescapeEqB (PE.subst (λ K → Whnf K) (whrDet* (red D , ⟦ W ⟧ₙ) (id (⊢A-red D) , whA)) ⟦ W ⟧ₙ) [A]f fA≡B)

  escapeEqB : ∀ {W A B} → ([A] : Γ / lε  ⊩¹B⟨ W ⟩ A)
            → Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / [A]
            → Γ / lε ⊢ A ≅ B
  escapeEqB {W = W} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' A≡B [F=F'] [G=G']) =
    ≅-red (red D) D' ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
  escapeEqB {W = W} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ _ B⇒B' αB' [A]t [A]f tA≡B fA≡B) =
    ≅-ϝ (escapeEqB [A]t tA≡B) (escapeEqB [A]f fA≡B)
   -- ≅-red (red D) (red B⇒B') ⟦ W ⟧ₙ (αₙ αB')
   --   (whescapeEqB ⟦ W ⟧ₙ
   --     (Bᵣ F G (idRed:*: (⊢B-red D)) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {_} {_} {≤ε}) [G] G-ext)
   --     (Bϝ _ (idRed:*: (⊢B-red B⇒B')) αB' (RedW W [A]t (τwfRed* D)) (RedW W [A]f (τwfRed* D))
   --         (RedConvW-l [A]t (τwfRed* D) {!!}) (RedConvW-l [A]f (τwfRed* D) {!!}))) 


  eqℕeqℕ : ∀ {A B} → Γ / lε ⊩ℕ A ≡ B
                   → Γ / lε ⊩ℕ ℕ ≡ B
  eqℕeqℕ (⊩ℕ≡ A B D') = ⊩ℕ≡ _ _ D'
  eqℕeqℕ (ϝ⊩ℕ≡ mε B⇒B' αB tA=B fA=B) = ϝ⊩ℕ≡ mε B⇒B' αB (eqℕeqℕ tA=B) (eqℕeqℕ fA=B)
                                                                             
  whescapeEqℕ : ∀ {A} → (⊢Γ : ⊢ Γ / lε)
    → Γ / lε ⊩ℕ ℕ ≡ A
             → Γ / lε ⊢ ℕ ≅ A
  whescapeEqℕ ⊢Γ (⊩ℕ≡ A B D') = ≅-red (id (ℕⱼ ⊢Γ)) D' ℕₙ ℕₙ (≅-ℕrefl ⊢Γ)
  whescapeEqℕ ⊢Γ (ϝ⊩ℕ≡ mε A⇒B αB tℕ=B fℕ=B) =
   ≅-ϝ (whescapeEqℕ (τCon _ _ _ _ ⊢Γ) tℕ=B) (whescapeEqℕ (τCon _ _ _ _ ⊢Γ) fℕ=B)
              
  escapeEqℕ : ∀ {A B} → ([A] : Γ / lε  ⊩ℕ A)
            → Γ / lε ⊩ℕ A ≡ B
            → Γ / lε ⊢ A ≅ B
  escapeEqℕ A⇒ℕ B⇒ℕ = ≅-trans (≅-red (red A⇒ℕ) (id (⊢B-red A⇒ℕ)) ℕₙ ℕₙ (≅-ℕrefl (wf (⊢B-red A⇒ℕ))))
                              (whescapeEqℕ (wf (⊢B-red A⇒ℕ)) (eqℕeqℕ B⇒ℕ))

  escapeEqNe : ∀ {A B} → ([A] : Γ / lε  ⊩ne A)
            → Γ / lε ⊩ne A ≡ B / [A]
            → Γ / lε ⊢ A ≅ B
  escapeEqNe (ne K D neK K≡K) (ne₌ [A] M D′ neM K≡M) =
    ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
  escapeEqNe (ne K D neK K≡K) (ϝ⊩ne≡ mε B⇒B' αB tC≡B fC≡B) =
    ≅-ϝ (escapeEqNe _ tC≡B) (escapeEqNe _ fC≡B) -- (≅-trans (≅-sym (≅-red (red D) (id (⊢B-red D)) (ne neK) (ne neK) (~-to-≅ K≡K)))
        --       (≅-ϝ (escapeEqNe _ tC≡B) (escapeEqNe _ fC≡B)))


  escapeTermEqNe : ∀ {A t u} → ([A] : Γ / lε  ⊩ne A)
                 → Γ / lε ⊩ne t ≡ u ∷ A / [A]
                 → Γ / lε ⊢ t ≅ u ∷ A
  escapeTermEqNe (ne K D neK K≡K)
                     (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
                 ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
                 (~-to-≅ₜ t≡u)
  escapeTermEqNe (ne K D neK K≡K)
                    (neₜ₌ k m d d′ (⊩neNfϝ-l {[A]t = [A]t} {[A]f = [A]f} αk (neNfₜ nem ⊢m m≡m) tkm fkm)) =
                    ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (αₙ αk) (ne nem)
                    (≅ₜ-ϝ (escapeTermEqNe [A]t tkm) (escapeTermEqNe [A]f fkm))
  escapeTermEqNe (ne K D neK K≡K)
                    (neₜ₌ k m d d′ (⊩neNfϝ-l {[A]t = [A]t} {[A]f = [A]f} αk (neNfϝ ⊢m αm tm fm) tkm fkm)) =
                    ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (αₙ αk) (αₙ αm)
                    (≅ₜ-ϝ (escapeTermEqNe [A]t tkm) (escapeTermEqNe [A]f fkm))
  escapeTermEqNe (ne K D neK K≡K)
                     (neₜ₌ k m d d′ (⊩neNfϝ-r {[A]t = [A]t} {[A]f = [A]f} (neNfₜ nek ⊢k k≡k) αm tkm fkm)) =
                    ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne nek) (αₙ αm)
                    (≅ₜ-ϝ (escapeTermEqNe [A]t tkm) (escapeTermEqNe [A]f fkm))
  escapeTermEqNe (ne K D neK K≡K)
                     (neₜ₌ k m d d′ (⊩neNfϝ-r {[A]t = [A]t} {[A]f = [A]f} (neNfϝ ⊢k αk tk fk) αm tkm fkm)) = 
                    ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (αₙ αk) (αₙ αm)
                    (≅ₜ-ϝ (escapeTermEqNe [A]t tkm) (escapeTermEqNe [A]f fkm))

  
  reflEqTermNe : ∀ {A t} ([A] : Γ / lε ⊩ne A)
             → Γ / lε ⊩ne t ∷ A / [A]
             → Γ / lε ⊩ne t ≡ t ∷ A / [A]
  reflEqTermNe (ne K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
             neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
  reflEqTermNe (ne K D neK K≡K) (neₜ k d (neNfϝ {[A]t = [A]t} ⊢k αk tk fk)) =
    neₜ₌ k k d d (⊩neNfϝ-l αk (neNfϝ ⊢k αk tk fk) (reflEqTermNe [A]t tk) (reflEqTermNe _ fk))


  eq𝔹eq𝔹 : ∀ {A B} → Γ / lε ⊩𝔹 A ≡ B
                   → Γ / lε ⊩𝔹 𝔹 ≡ B
  eq𝔹eq𝔹 (⊩𝔹≡ A B D') = ⊩𝔹≡ _ _ D'
  eq𝔹eq𝔹 (ϝ⊩𝔹≡ mε B⇒B' αB tA=B fA=B) = ϝ⊩𝔹≡ mε B⇒B' αB (eq𝔹eq𝔹 tA=B) (eq𝔹eq𝔹 fA=B)
                                                                             
  whescapeEq𝔹 : ∀ {A} → (⊢Γ : ⊢ Γ / lε)
              → Γ / lε ⊩𝔹 𝔹 ≡ A
             → Γ / lε ⊢ 𝔹 ≅ A
  whescapeEq𝔹 ⊢Γ (⊩𝔹≡ A B D') = ≅-red (id (𝔹ⱼ ⊢Γ)) D' 𝔹ₙ 𝔹ₙ (≅-𝔹refl ⊢Γ)
  whescapeEq𝔹 ⊢Γ (ϝ⊩𝔹≡ mε A⇒B αB t𝔹=B f𝔹=B) =
   ≅-ϝ (whescapeEq𝔹 (τCon _ _ _ _ ⊢Γ) t𝔹=B) (whescapeEq𝔹 (τCon _ _ _ _ ⊢Γ) f𝔹=B)
              
  escapeEq𝔹 : ∀ {A B} → ([A] : Γ / lε  ⊩𝔹 A)
            → Γ / lε ⊩𝔹 A ≡ B
            → Γ / lε ⊢ A ≅ B
  escapeEq𝔹 A⇒𝔹 B⇒𝔹 = ≅-trans (≅-red (red A⇒𝔹) (id (⊢B-red A⇒𝔹)) 𝔹ₙ 𝔹ₙ (≅-𝔹refl (wf (⊢B-red A⇒𝔹))))
                              (whescapeEq𝔹 (wf (⊢B-red A⇒𝔹)) (eq𝔹eq𝔹 B⇒𝔹))

    
open LogRel public using (Uᵣ; ℕᵣ; 𝔹ᵣ ; ne; Bᵣ; B₌; Bϝ ; emb; Uₜ; Uₜ₌ ; ϝᵣ)

-- Patterns for the non-records of Π
pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern Σₜ p d pProd p≅p [fst] [snd] = p , d , pProd , p≅p , ([fst] , [snd])
pattern Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡] = p , r , d , d′ , pProd , rProd , p≅r , [t] , [u] , ([fstp] , [fstr] , [fst≡] , [snd≡])

pattern Uᵣ′ a b c = Uᵣ (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Bᵣ′ W a b c d e f g h i = Bᵣ W (Bᵣ a b c d e f g h i)
pattern Πᵣ′ a b c d e f g h i = Bᵣ′ BΠ a b c d e f g h i
pattern Σᵣ′ a b c d e f g h i = Bᵣ′ BΣ a b c d e f g h i

logRelRec : ∀ j {j′} → j′ < j → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit j = LogRel.kit j (logRelRec j)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_/_⊩′⟨_⟩U : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) → Set
Γ / lε ⊩′⟨ j ⟩U = Γ / lε ⊩U where open LogRelKit (kit j)

_/_⊩′⟨_⟩B⟨_⟩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) (W : BindingType) → Term ℓ → Set
Γ / lε ⊩′⟨ j ⟩B⟨ W ⟩ A = Γ / lε ⊩B⟨ W ⟩ A where open LogRelKit (kit j)

_/_⊩⟨_⟩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) → Term ℓ → Set
Γ / lε ⊩⟨ j ⟩ A = Γ / lε ⊩ A where open LogRelKit (kit j)

_/_⊩⟨_⟩_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) (A B : Term ℓ) → Γ / lε ⊩⟨ j ⟩ A → Set
Γ / lε ⊩⟨ j ⟩ A ≡ B / [A] = Γ / lε ⊩ A ≡ B / [A] where open LogRelKit (kit j)

_/_⊩⟨_⟩_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) (t A : Term ℓ) → Γ / lε ⊩⟨ j ⟩ A → Set
Γ / lε ⊩⟨ j ⟩ t ∷ A / [A] = Γ / lε ⊩ t ∷ A / [A] where open LogRelKit (kit j)

_/_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (j : TypeLevel) (t u A : Term ℓ) → Γ / lε ⊩⟨ j ⟩ A → Set
Γ / lε ⊩⟨ j ⟩ t ≡ u ∷ A / [A] = Γ / lε ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit j)


-- TyPermLog : ∀ {k A n} ([A] :  Γ / lε ⊩⟨ k ⟩ A) → Γ / (permutε n lε) ⊩⟨ k ⟩ A
-- TyPermLog (Uᵣ′ k′ k< ⊢Γ) = Uᵣ′ k′ k< (ConPerm _ _ ⊢Γ) --  Uᵣ′ k′ k< (τCon _ _ _ _ ⊢Γ)
-- TyPermLog (ℕᵣ [ ⊢A , ⊢ℕ , D ]) = ℕᵣ ([ TyPerm _ _ ⊢A , TyPerm _ _ ⊢ℕ , RedPerm* D ])
-- TyPermLog (Emptyᵣ [ ⊢A , ⊢Empty , D ]) = Emptyᵣ ([ TyPerm _ _ ⊢A , TyPerm _ _ ⊢Empty , RedPerm* D ]) 
-- TyPermLog (Unitᵣ [ ⊢A , ⊢Unit , D ]) = Unitᵣ ([ TyPerm _ _ ⊢A , TyPerm _ _ ⊢Unit , RedPerm* D ])
-- TyPermLog (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) = ne (ne K [ TyPerm _ _ ⊢A , TyPerm _ _ ⊢K , RedPerm* D ] neK {!!}) -- (~-Perm K≡K))
-- TyPermLog (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) = {!!}
-- TyPermLog (emb {l} {lε} {A}  0<1 [A]) = emb 0<1 (TyPermLog [A]) 
-- TyPermLog {n = n} (ϝᵣ {m = m} {mε = mε} [ ⊢A , ⊢B , D ] αB  tB fB) = ϝᵣ {_} {_} {_} {_} {_} {_} {_} {_} {m} {permutNotInLConNat _ _ _ mε} ([ TyPerm _ _ ⊢A , TyPerm _ _ ⊢B , RedPerm* D ]) {!!} (TyPermLog  tB) (TyPermLog fB)


-- τTyLog : ∀ {k A n b nε} ([A] :  Γ / lε ⊩⟨ k ⟩ A) → Γ / (⊢ₗ• l lε n b nε) ⊩⟨ k ⟩ A
-- τTyLog (Uᵣ′ k′ k< ⊢Γ) = Uᵣ′ k′ k< (τCon _ _ _ _ ⊢Γ)
-- τTyLog (ℕᵣ [ ⊢A , ⊢ℕ , D ]) = ℕᵣ ([ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢ℕ , τRed* D ])
-- τTyLog (Emptyᵣ [ ⊢A , ⊢Empty , D ]) = Emptyᵣ ([ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢Empty , τRed* D ]) --  Emptyᵣ ([ ⊢A , ⊢Empty , ⇒*-comp D' D ])
-- τTyLog (Unitᵣ [ ⊢A , ⊢Unit , D ]) = Unitᵣ ([ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢Unit , τRed* D ]) --  Unitᵣ ([ ⊢A , ⊢Unit , ⇒*-comp D' D ])
-- τTyLog (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) = ne (ne K ([ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢K , τRed* D ]) neK (~-τ K≡K)) --  ne (ne K ([ ⊢A , ⊢K , ⇒*-comp D' D ]) neK K≡K)
-- τTyLog (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) =
--      Bᵣ W (Bᵣ F G ([ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢Π , τRed* D ]) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A)
--        (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ₗ-rev ≤ε}) [G] G-ext)
-- τTyLog (emb {l} {lε} {A}  0<1 [A]) = emb 0<1 (τTyLog [A]) 
-- τTyLog (ϝᵣ [ ⊢B , ⊢C , D ] αB  tB fB) = {!!} --  ϝᵣ ([ ⊢A , ⊢C , ⇒*-comp D' D ]) αB tB fB 
