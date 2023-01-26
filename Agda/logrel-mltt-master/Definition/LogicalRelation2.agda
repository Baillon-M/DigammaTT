{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation2 {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (_∷_)
open import Definition.Untyped.Properties
open import Definition.Typed.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Agda.Primitive

open import Tools.Nat
open import Tools.Product
open import Tools.Embedding
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Nat
    Γ : Con Term ℓ

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reduction to a whnf:

record _/_⊩wh_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) : Set
  where
  constructor wh
  field
    B : Term ℓ
    D : Γ / lε ⊢ A :⇒*: B
    whB : Whnf {lε = lε} B

record _/_⊩wh_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) : Set
  where
  constructor whₜ
  field
    u : Term ℓ
    D : Γ / lε ⊢ t :⇒*: u ∷ A
    whu : Whnf {lε = lε} u

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
record _/_⊩ne_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set
  where
  constructor ne₌
  open _/_⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ / lε ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ / lε ⊢ (_/_⊩ne_.K [A]) ~ M ∷ U

-- Neutral term in WHNF
record _/_⊩neNf_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k A : Term ℓ) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ / lε ⊢ k ∷ A
    k≡k  : Γ / lε ⊢ k ~ k ∷ A
    
-- Neutral term
record _/_⊩ne_∷_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
  inductive
  constructor neₜ
  open _/_⊩ne_ [A]
  field
    k   : Term ℓ
    d   : Γ / lε ⊢ t :⇒*: k ∷ K
    nf  : Γ / lε ⊩neNf k ∷ K
 
-- Neutral term equality in WHNF
record _/_⊩neNf_≡_∷_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (k m A : Term ℓ) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ / lε ⊢ k ~ m ∷ A

-- Neutral term equality
record _/_⊩ne_≡_∷_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
  constructor neₜ₌
  open _/_⊩ne_ [A]
  field
    k m : Term ℓ
    d   : Γ / lε ⊢ t :⇒*: k ∷ K
    d′  : Γ / lε ⊢ u :⇒*: m ∷ K
    nf  : Γ / lε ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_/_⊩ℕ_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩ℕ A = Γ / lε ⊢ A :⇒*: ℕ

-- Natural number type equality
_/_⊩ℕ_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
Γ / lε ⊩ℕ A ≡ B = Γ / lε ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  data _/_⊩ℕ_∷ℕ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
    ℕₜ : ∀ (n : Term ℓ)
          (d : Γ / lε ⊢ t :⇒*: n ∷ ℕ)
          (n≡n : Γ / lε ⊢ n ≅ n ∷ ℕ)
          (prop : Natural-prop Γ lε n)
          → Γ / lε ⊩ℕ t ∷ℕ

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n : Term ℓ) → Set where
    sucᵣ  : ∀ {n} → Γ / lε ⊩ℕ n ∷ℕ → Natural-prop Γ lε (suc n)
    zeroᵣ : Natural-prop Γ lε zero
    ne    : ∀ {n} → Γ / lε ⊩neNf n ∷ ℕ → Natural-prop Γ lε n


mutual
  -- Natural number term equality
  data _/_⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : ∀ (t u : Term ℓ) → Set where
    ℕₜ₌ :  ∀ {t u : Term ℓ}
      (k k′ : Term ℓ)
      (d : Γ / lε ⊢ t :⇒*: k  ∷ ℕ)
      (d′ : Γ / lε ⊢ u :⇒*: k′ ∷ ℕ)
      (k≡k′ : Γ / lε ⊢ k ≅ k′ ∷ ℕ)
      (prop : [Natural]-prop Γ lε k k′)
      → Γ / lε ⊩ℕ t ≡ u ∷ℕ

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (n n′ : Term ℓ) → Set where
    sucᵣ  : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ lε (suc n) (suc n′)
    zeroᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Natural]-prop Γ lε zero zero
    ne    : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ lε n n′

-- Natural extraction from term WHNF property
natural : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Natural-prop Γ lε n → Natural {_} {l} {lε} n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK
-- natural (ne (neNfϝ x αn x₂ x₃)) = neα αn
-- natural (ℕϝ ⊢n αn nt nf) = neα αn

-- Natural extraction from term equality WHNF property
split : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Natural]-prop Γ lε a b → Natural {_} {l} {lε} a × Natural {_} {l} {lε} b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM


-- Boolean type
_/_⊩𝔹_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩𝔹 A = Γ / lε ⊢ A :⇒*: 𝔹

-- Boolean type equality
_/_⊩𝔹_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
Γ / lε ⊩𝔹 A ≡ B = Γ / lε ⊢ B ⇒* 𝔹

mutual
  -- Boolean term
  data _/_⊩𝔹_∷𝔹 (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
   𝔹ₜ : ∀ (b : Term ℓ)
          (d : Γ / lε ⊢ t :⇒*: b ∷ 𝔹)
          (n≡n : Γ / lε ⊢ b ≅ b ∷ 𝔹)
          (prop : Boolean-prop Γ lε b)
        → Γ / lε ⊩𝔹 t ∷𝔹

  -- WHNF property of boolean terms
  data Boolean-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (b : Term ℓ) → Set where
    trueᵣ : Boolean-prop Γ lε true
    falseᵣ : Boolean-prop Γ lε false
    ne    : ∀ {b} → Γ / lε ⊩neNf b ∷ 𝔹 → Boolean-prop Γ lε b

mutual
  -- Boolean term equality
  data _/_⊩𝔹_≡_∷𝔹 (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
   𝔹ₜ₌ : ∀ (b b′ : Term ℓ)
           (d : Γ / lε ⊢ t :⇒*: b ∷ 𝔹)
           (d′ : Γ / lε ⊢ u :⇒*: b′ ∷ 𝔹)
           (b≡b′ : Γ / lε ⊢ b ≅ b′ ∷ 𝔹)
           (prop : [Boolean]-prop Γ lε b b′)
           → Γ / lε ⊩𝔹 t ≡ u ∷𝔹
           
  -- WHNF property of Natural number term equality
  data [Boolean]-prop (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) (n n′ : Term ℓ) → Set where
    trueᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Boolean]-prop Γ lε true true
    falseᵣ : ∀ {l : LCon} {lε : ⊢ₗ l} → [Boolean]-prop Γ lε false false
    ne    : ∀ {l : LCon} {lε : ⊢ₗ l} {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ 𝔹 → [Boolean]-prop Γ lε n n′

-- Boolean extraction from term WHNF property
boolean : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Boolean-prop Γ lε n → Boolean {_} {l} {lε} n
boolean trueᵣ = trueₙ
boolean falseᵣ = falseₙ
boolean (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Boolean from term equality WHNF property
bsplit : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Boolean]-prop Γ lε a b → Boolean {_} {l} {lε} a × Boolean {_} {l} {lε} b
bsplit trueᵣ = trueₙ , trueₙ
bsplit falseᵣ = falseₙ , falseₙ
bsplit (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

toLevel : TypeLevel → Level
toLevel ⁰ = lzero
toLevel ¹ = lsuc lzero

-- Logical relation

record LogRelKit (lev : Level) : Set (lsuc (lsuc lev)) where
  constructor Kit
  field
    _/_⊩U : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) → Set (lsuc lev)
    _/_⊩B⟨_⟩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) → Term ℓ → Set (lsuc lev)

    _/_⊩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) → Term ℓ → Set (lsuc lev)
    _/_⊩_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩ A → Set lev
    _/_⊩_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩ A → Set lev
    _/_⊩_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩ A → Set lev

module LogRel (lev : TypeLevel) (rec : ∀ {lev′} → lev′ < lev → LogRelKit (toLevel lev)) where

  record _/_⊩¹U (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : Set (lsuc (lsuc (toLevel lev))) where
    constructor Uᵣ
    field
      lev′ : TypeLevel
      l< : lev′ < lev
      ⊢Γ : ⊢ Γ / lε

  -- Universe type equality
  record _/_⊩¹U≡_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (B : Term ℓ) : Set (lsuc (toLevel lev)) where
    constructor U₌
    field
      B≡U : B PE.≡ U

  -- Universe term
  record _/_⊩¹U_∷U/_ {lev′} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) (l< : lev′ < lev) : Set (lsuc (toLevel lev)) where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term ℓ
      d     : Γ / lε ⊢ t :⇒*: A ∷ U
      typeA : Type {_} {_} {lε} A
      A≡A   : Γ / lε ⊢ A ≅ A ∷ U
      [t]   : Γ / lε ⊩ t

  -- Universe term equality
  record _/_⊩¹U_≡_∷U/_ {lev′} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) (l< : lev′ < lev) : Set (lsuc (toLevel lev)) where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term ℓ
      d     : Γ / lε ⊢ t :⇒*: A ∷ U
      d′    : Γ / lε ⊢ u :⇒*: B ∷ U
      typeA : Type {_} {_} {lε} A
      typeB : Type {_} {_} {lε} B
      A≡B   : Γ / lε ⊢ A ≅ B ∷ U
      [t]   : Γ / lε ⊩ t
      [u]   : Γ / lε ⊩ u
      [t≡u] : Γ / lε ⊩ t ≡ u / [t]

  RedRel : ∀ {ℓ : Nat} → Set (lsuc (lsuc (lsuc (toLevel lev))))
  RedRel {ℓ = ℓ} = Con Term ℓ → {l : LCon} → (lε : ⊢ₗ l) → Term ℓ → (Term ℓ → Set (lsuc (toLevel lev))) → (Term ℓ → Set (lsuc (toLevel lev))) → (Term ℓ → Term ℓ → Set (lsuc (toLevel lev))) → Set (lsuc (lsuc (toLevel lev)))

  record _/_⊩⁰_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) (_/_⊩_▸_▸_▸_ : RedRel {ℓ}) : Set (lsuc (lsuc (toLevel lev))) where
    inductive
    eta-equality
    constructor LRPack
    field
      ⊩Eq : Term ℓ → Set (lsuc (toLevel lev))
      ⊩Term : Term ℓ → Set (lsuc (toLevel lev))
      ⊩EqTerm : Term ℓ → Term ℓ → Set (lsuc (toLevel lev))
      ⊩LR : Γ / lε ⊩ A ▸ ⊩Eq ▸ ⊩Term ▸ ⊩EqTerm

  _/_⊩⁰_≡_/_ : {R : RedRel} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩⁰ A / R → Set (lsuc (toLevel lev))
  Γ / lε ⊩⁰ A ≡ B / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩Eq B

  _/_⊩⁰_∷_/_ : {R : RedRel} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩⁰ A / R → Set (lsuc (toLevel lev))
  Γ / lε ⊩⁰ t ∷ A / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩Term t

  _/_⊩⁰_≡_∷_/_ : {R : RedRel} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩⁰ A / R → Set (lsuc (toLevel lev))
  Γ / lε ⊩⁰ t ≡ u ∷ A / LRPack ⊩Eq ⊩Term ⊩EqTerm ⊩Red = ⊩EqTerm t u

  record _/_⊩¹B⟨_⟩_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) (A : Term ℓ) (R : RedRel {ℓ}) : Set (lsuc (lsuc (toLevel lev))) where
    inductive
    eta-equality
    constructor Bᵣ
    field
      F : Term ℓ
      G : Term (1+ ℓ)
      D : Γ / lε ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
      ⊢F : Γ / lε ⊢ F
      ⊢G : Γ ∙ F / lε ⊢ G
      A≡A : Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
      [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ / lε) → Δ / lε ⊩⁰ U.wk ρ F / R
      [G] : ∀ {ρ Δ a}
          → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
          → _/_⊩⁰_∷_/_ Δ lε a (U.wk ρ F) ([F] [ρ] ⊢Δ)
          → Δ / lε ⊩⁰ U.wk (lift ρ) G [ a ] / R
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
            → ([a] : _/_⊩⁰_∷_/_ Δ lε a ((U.wk ρ) F) (([F] [ρ]) ⊢Δ))
            → ([b] : _/_⊩⁰_∷_/_ Δ lε b ((U.wk ρ) F) (([F] [ρ]) ⊢Δ))
            → _/_⊩⁰_≡_∷_/_ Δ lε a b ((U.wk ρ) F) (([F] [ρ]) ⊢Δ)
            → Δ / lε ⊩⁰ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

  record _/_⊩¹B⟨_⟩_≡_/_ {R : RedRel {ℓ}} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) (A B : Term ℓ)
                        ([A] : Γ / lε ⊩¹B⟨ W ⟩ A / R) : Set (lsuc (toLevel lev)) where
    inductive
    eta-equality
    constructor Π₌
    open _/_⊩¹B⟨_⟩_/_ [A]
    field
      F′     : Term ℓ
      G′     : Term (1+ ℓ)
      D′     : Γ / lε ⊢ B ⇒*  ⟦ W ⟧ F′ ▹ G′
      A≡B    : Γ / lε ⊢  ⟦ W ⟧ F ▹ G ≅  ⟦ W ⟧ F′ ▹ G′
      [F≡F′] : ∀ {ρ Δ}
             → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
             → Δ / lε ⊩⁰ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
      [G≡G′] : ∀ {ρ Δ a}
             → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
             → ([a] : _/_⊩⁰_∷_/_ Δ lε a ((U.wk ρ) F) (([F] [ρ]) ⊢Δ))
             → Δ / lε ⊩⁰ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

  -- Term of Π-type
  _/_⊩¹Π_∷_/_ : {R : RedRel {ℓ}} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A / R) →
                Set (lsuc (toLevel lev))
  Γ / lε ⊩¹Π t ∷ A / (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
    ∃ λ f → (Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G)
          × Function {_} {_} {lε} f
          × Γ / lε ⊢ f ≅ f ∷ Π F ▹ G
          × (∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
              ([a] : _/_⊩⁰_∷_/_ Δ lε a ((U.wk ρ) F) (([F] [ρ]) ⊢Δ))
              ([b] : _/_⊩⁰_∷_/_ Δ lε b ((U.wk ρ) F) (([F] [ρ]) ⊢Δ)) 
              ([a≡b] :  _/_⊩⁰_≡_∷_/_ Δ lε a b ((U.wk ρ) F) (([F] [ρ]) ⊢Δ)) -- Δ / lε ⊩⁰ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → Δ / lε ⊩⁰ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
          × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
            → ([a] : _/_⊩⁰_∷_/_ Δ lε a ((U.wk ρ) F) (([F] [ρ]) ⊢Δ)) -- Δ / lε ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
            → Δ / lε ⊩⁰ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
  -- Issue: Agda complains about record use not being strictly positive.
  --        Therefore we have to use ×


  -- Term equality of Π-type
  _/_⊩¹Π_≡_∷_/_ : {R : RedRel {ℓ}} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A / R)
                  → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹Π t ≡ u ∷ A / (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
    let [A] = Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
    in  ∃₂ λ f g →
        (Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G)
    ×   (Γ / lε ⊢ u :⇒*: g ∷ Π F ▹ G)
    ×   (Function {_} {_} {lε} f)
    ×   (Function {_} {_} {lε} g)
    ×   (Γ / lε ⊢ f ≅ g ∷ Π F ▹ G)
    ×   (Γ / lε ⊩¹Π t ∷ A / [A])
    ×   (Γ / lε ⊩¹Π u ∷ A / [A])
    ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
        → ([a] : _/_⊩⁰_∷_/_ Δ lε a ((U.wk ρ) F) (([F] [ρ]) ⊢Δ)) -- ([a] : Δ / lε ⊩⁰ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
        → Δ / lε ⊩⁰ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
  -- Issue: Same as above.

    -- Term reducibility of Σ-type
  _/_⊩¹Σ_∷_/_ : {R : RedRel {ℓ}} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΣ ⟩ A / R)
                  → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹Σ t ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ p → (Γ / lε ⊢ t :⇒*: p ∷ Σ F ▹ G)
            × (Product p)
            × (Γ / lε ⊢ p ≅ p ∷ Σ F ▹ G)
            × (Σ (_/_⊩⁰_∷_/_ Γ lε (fst p) (U.wk id F) ([F] id (wf ⊢F)))
                 λ [fst]
                   → Γ / lε ⊩⁰ snd p ∷ (U.wk (lift id) G [ fst p ]) / [G] id (wf ⊢F) [fst])

    -- Term equality of Σ-type
  _/_⊩¹Σ_≡_∷_/_ : {R : RedRel {ℓ}} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΣ ⟩ A / R)
                  → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹Σ t ≡ u ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ p r → Γ / lε ⊢ t :⇒*: p ∷ Σ F ▹ G
               × Γ / lε ⊢ u :⇒*: r ∷ Σ F ▹ G
               × Product p
               × Product r
               × Γ / lε ⊢ p ≅ r ∷ Σ F ▹ G
               × Γ / lε ⊩¹Σ t ∷ A / [A]
               × Γ / lε ⊩¹Σ u ∷ A / [A]
               × (Σ (Γ / lε ⊩⁰ fst p ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
                    → Γ / lε ⊩⁰ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / lε ⊩⁰ fst p ≡ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / lε ⊩⁰ snd p ≡ snd r ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fstp])

  -- Logical relation definition
  data _/_⊩LR_▸_▸_▸_ : RedRel {ℓ} where
    LRU : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (⊢Γ : ⊢ Γ / lε) → (lev' : TypeLevel) → (l< : lev' < lev)
      → Γ / lε ⊩LR U
      ▸ (λ B → Γ / lε ⊩¹U≡ B)
      ▸ (λ t → Γ / lε ⊩¹U t ∷U/ l<)
      ▸ (λ t u → Γ / lε ⊩¹U t ≡ u ∷U/ l<)
    LRℕ : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) {A} → Γ / lε ⊩ℕ A → Γ / lε ⊩LR A
      ▸ (λ B → ι′ (Γ / lε ⊩ℕ A ≡ B))
      ▸ (λ t → ι′ (Γ / lε ⊩ℕ t ∷ℕ))
      ▸ (λ t u → ι′ (Γ / lε ⊩ℕ t ≡ u ∷ℕ))
    LRne : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) {A} → (neA : Γ / lε ⊩ne A) → Γ / lε ⊩LR A
      ▸ (λ B → ι′ (Γ / lε ⊩ne A ≡ B / neA))
      ▸ (λ t → ι′ (Γ / lε ⊩ne t ∷ A / neA))
      ▸ (λ t u → ι′ (_/_⊩ne_≡_∷_/_ Γ lε t u A neA))
    LRΠ : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) {A} → (BA : Γ / lε ⊩¹B⟨ BΠ ⟩ A / (_/_⊩LR_▸_▸_▸_))
      → Γ / lε ⊩LR A
      ▸ (λ B → Γ / lε ⊩¹B⟨ BΠ ⟩ A ≡ B / BA)
      ▸ (λ t → Γ / lε ⊩¹Π t ∷ A / BA)
      ▸ (λ t u → Γ / lε ⊩¹Π t ≡ u ∷ A / BA)
    LRemb : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) {A lev′} (l< : lev′ < lev) (let open LogRelKit (rec l<))
          ([A] : Γ / lε ⊩ A)
          → Γ / lε ⊩LR A
      ▸ (λ B → ι (Γ / lε ⊩ A ≡ B / [A]))
      ▸ (λ t → ι (Γ / lε ⊩ t ∷ A / [A]))
      ▸ (λ t u → ι (Γ / lε ⊩ t ≡ u ∷ A / [A]))
    LRϝ : ∀ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l)
            {A m mε}
            (WhA : Γ / lε ⊩wh A)
            {tA≡ tAₜ tAₜ≡ fA≡ fAₜ fAₜ≡}
            → Γ / (⊢ₗ• l lε m Btrue mε) ⊩LR A ▸ tA≡ ▸ tAₜ ▸ tAₜ≡
            → Γ / (⊢ₗ• l lε m Bfalse mε) ⊩LR A ▸ fA≡ ▸ fAₜ ▸ fAₜ≡
            → Γ / lε ⊩LR A
            ▸ (λ B → (Γ / lε ⊩wh B) × (tA≡ B) × (fA≡ B))
            ▸ (λ t → (Γ / lε ⊩wh t ∷ A) × (tAₜ t) × (fAₜ t))
            ▸ (λ t u → (Γ / lε ⊩wh t ∷ A) × (Γ / lε ⊩wh u ∷ A) × (tAₜ≡ t u) × (fAₜ≡ t u))

  _/_⊩¹_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) → (A : Term ℓ) → Set (lsuc (lsuc (toLevel lev)))
  Γ / lε ⊩¹ A = Γ / lε ⊩⁰ A / _/_⊩LR_▸_▸_▸_

  _/_⊩¹_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩¹ A → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹ A ≡ B / [A] = Γ / lε ⊩⁰ A ≡ B / [A]

  _/_⊩¹_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩¹ A → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹ t ∷ A / [A] = Γ / lε ⊩⁰ t ∷ A / [A]

  _/_⊩¹_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩¹ A → Set (lsuc (toLevel lev))
  Γ / lε ⊩¹ t ≡ u ∷ A / [A] = Γ / lε ⊩⁰ t ≡ u ∷ A / [A]

open LogRel public using (Uᵣ; Bᵣ; Π₌; U₌ ; Uₜ; Uₜ₌ ; LRU ; LRℕ ; LRne ; LRΠ ; LRemb ; LRPack)

pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern ℕᵣ a = LRPack _ _ _ (LRℕ a)
pattern emb′ a b = LRPack _ _ _ (LRemb a b)
pattern Uᵣ′ a b c = LRPack _ _ _ (LRU c a b)
pattern ne′ a b c d = LRPack _ _ _ (LRne (ne a b c d))
-- pattern Πᵣ′ a b c d e f g h i = LRPack _ _ _ (LRΠ (Πᵣ a b c d e f g h i))

kit₀ : LogRelKit (lsuc (lzero))
kit₀ = Kit _/_⊩¹U (λ Γ lε W A → Γ / lε ⊩¹B⟨ W ⟩ A / _/_⊩LR_▸_▸_▸_) _/_⊩¹_ _/_⊩¹_≡_/_ _/_⊩¹_∷_/_ _/_⊩¹_≡_∷_/_
  where open LogRel ⁰ (λ ())

logRelRec : ∀ lev {lev′} → lev′ < lev → LogRelKit (toLevel lev)
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = kit₀

kit : ∀ (lev : TypeLevel) → LogRelKit (lsuc (toLevel lev))
kit lev = Kit _/_⊩¹U (λ Γ lε W A → Γ / lε ⊩¹B⟨ W ⟩ A / _/_⊩LR_▸_▸_▸_) _/_⊩¹_ _/_⊩¹_≡_/_ _/_⊩¹_∷_/_ _/_⊩¹_≡_∷_/_
  where open LogRel lev (logRelRec lev)

-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

record _/_⊩′⟨_⟩U (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) : Set where
  constructor Uᵣ
  field
    lev′ : TypeLevel
    l< : lev′ < lev
    ⊢Γ : ⊢ Γ / lε

-- _/_⊩′⟨_⟩Π_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) → Term ℓ → Set (lsuc (lsuc (toLevel lev)))
-- Γ / lε ⊩′⟨ lev ⟩Π A = Γ / lε ⊩Π A where open LogRelKit (kit lev)

_/_⊩⟨_⟩_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) → Term ℓ → Set (lsuc (lsuc (toLevel lev)))
Γ / lε ⊩⟨ lev ⟩ A = Γ / lε ⊩ A where open LogRelKit (kit lev)

_/_⊩⟨_⟩_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) (A B : Term ℓ) → Γ / lε ⊩⟨ lev ⟩ A → Set (lsuc (toLevel lev))
Γ / lε ⊩⟨ lev ⟩ A ≡ B / [A] = Γ / lε ⊩ A ≡ B / [A] where open LogRelKit (kit lev)

_/_⊩⟨_⟩_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) (t A : Term ℓ) → Γ / lε ⊩⟨ lev ⟩ A → Set (lsuc (toLevel lev))
Γ / lε ⊩⟨ lev ⟩ t ∷ A / [A] = Γ / lε ⊩ t ∷ A / [A] where open LogRelKit (kit lev)

_/_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (lev : TypeLevel) (t u A : Term ℓ) → Γ / lε ⊩⟨ lev ⟩ A → Set (lsuc (toLevel lev))
Γ / lε ⊩⟨ lev ⟩ t ≡ u ∷ A / [A] = Γ / lε ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit lev)
