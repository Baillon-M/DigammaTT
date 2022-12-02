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
record _/_⊩ne_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) ([A] : Γ / lε ⊩ne A) : Set where
  constructor ne₌
  open _/_⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ / lε ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ / lε ⊢ K ~ M ∷ U

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

-- Natural extraction from term WHNF property
natural : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Natural-prop Γ lε n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Natural]-prop Γ lε a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_/_⊩Empty_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩Empty A = Γ / lε ⊢ A :⇒*: Empty

-- Empty type equality
_/_⊩Empty_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
Γ / lε ⊩Empty A ≡ B = Γ / lε ⊢ B ⇒* Empty

-- WHNF property of absurd terms
data Empty-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n : Term ℓ) → Set where
  ne    : ∀ {n} → Γ / lε ⊩neNf n ∷ Empty → Empty-prop Γ lε n

-- Empty term
record _/_⊩Empty_∷Empty (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
  inductive
  constructor Emptyₜ
  field
    n : Term ℓ
    d : Γ / lε ⊢ t :⇒*: n ∷ Empty
    n≡n : Γ / lε ⊢ n ≅ n ∷ Empty
    prop : Empty-prop Γ lε n

data [Empty]-prop (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) : (n n′ : Term ℓ) → Set where
  ne    : ∀ {n n′} → Γ / lε ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ lε n n′

-- Empty term equality
record _/_⊩Empty_≡_∷Empty (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
  inductive
  constructor Emptyₜ₌
  field
    k k′ : Term ℓ
    d : Γ / lε ⊢ t :⇒*: k  ∷ Empty
    d′ : Γ / lε ⊢ u :⇒*: k′ ∷ Empty
    k≡k′ : Γ / lε ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ lε k k′

empty : ∀ {l : LCon} {lε : ⊢ₗ l} {n} → Empty-prop Γ lε n → Neutral n
empty (ne (neNfₜ neK _ _)) = neK

esplit : ∀ {l : LCon} {lε : ⊢ₗ l} {a b} → [Empty]-prop Γ lε a b → Neutral a × Neutral b
esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Reducibility of Unit

-- Unit type
_/_⊩Unit_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A : Term ℓ) → Set
Γ / lε ⊩Unit A = Γ / lε ⊢ A :⇒*: Unit

-- Unit type equality
_/_⊩Unit_≡_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Set
Γ / lε ⊩Unit A ≡ B = Γ / lε ⊢ B ⇒* Unit

record _/_⊩Unit_∷Unit (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t : Term ℓ) : Set where
  inductive
  constructor Unitₜ
  field
    n : Term ℓ
    d : Γ / lε ⊢ t :⇒*: n ∷ Unit
    prop : Whnf {l} {lε} n

-- Unit term equality
record _/_⊩Unit_≡_∷Unit (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u : Term ℓ) : Set where
  constructor Unitₜ₌
  field
    ⊢t : Γ / lε ⊢ t ∷ Unit
    ⊢u : Γ / lε ⊢ u ∷ Unit

-- Type levels

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
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ / lε → Δ / lε ⊩¹ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
            → Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ / lε ⊩¹ U.wk (lift ρ) G [ a ]
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
              → ([a] : Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ / lε ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / lε ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ / lε ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

    -- B-type equality
    record _/_⊩¹B⟨_⟩_≡_/_ (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (W : BindingType) (A B : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ W ⟩ A) : Set where
      inductive
      constructor B₌
      eta-equality
      open _/_⊩¹B⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ / lε ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
               → Δ / lε ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
               → ([a] : Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ / lε ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _/_⊩¹Π_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_∷_/_ {ℓ} Γ lε t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ f → Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G
            × Function f
            × Γ / lε ⊢ f ≅ f ∷ Π F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
              ([a] : Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ / lε ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ / lε ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / lε ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
              → ([a] : Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / lε ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _/_⊩¹Π_≡_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_≡_∷_/_  {ℓ} Γ lε t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ f g → Γ / lε ⊢ t :⇒*: f ∷ Π F ▹ G
               × Γ / lε ⊢ u :⇒*: g ∷ Π F ▹ G
               × Function f
               × Function g
               × Γ / lε ⊢ f ≅ g ∷ Π F ▹ G
               × Γ / lε ⊩¹Π t ∷ A / [A]
               × Γ / lε ⊩¹Π u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε)
                 ([a] : Δ / lε ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ / lε ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _/_⊩¹Σ_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) ([A] : Γ / lε ⊩¹B⟨ BΣ ⟩ A) → Set
    Γ / lε ⊩¹Σ t ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ p → Γ / lε ⊢ t :⇒*: p ∷ Σ F ▹ G
            × Product p
            × Γ / lε ⊢ p ≅ p ∷ Σ F ▹ G
            × (Σ (Γ / lε ⊩¹ fst p ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst]
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
               × (Σ (Γ / lε ⊩¹ fst p ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
                    → Γ / lε ⊩¹ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / lε ⊩¹ fst p ≡ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / lε ⊩¹ snd p ≡ snd r ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fstp])

    -- Logical relation definition
    data _/_⊩¹_ (Γ : Con Term ℓ) : ∀ {l : LCon} (lε : ⊢ₗ l) → Term ℓ → Set where
      Uᵣ  : Γ / lε ⊩¹U → Γ / lε ⊩¹ U
      ℕᵣ  : ∀ {A} → Γ / lε ⊩ℕ A → Γ / lε ⊩¹ A
      Emptyᵣ : ∀ {A} → Γ / lε ⊩Empty A → Γ / lε ⊩¹ A
      Unitᵣ : ∀ {A} → Γ / lε ⊩Unit A → Γ / lε ⊩¹ A
      ne  : ∀ {A} → Γ / lε ⊩ne A → Γ / lε ⊩¹ A
      Bᵣ  : ∀ {A} W → Γ / lε ⊩¹B⟨ W ⟩ A → Γ / lε ⊩¹ A
      emb : ∀ {A j′} (j< : j′ < j) (let open LogRelKit (rec j<))
            ([A] : Γ / lε ⊩ A) → Γ / lε ⊩¹ A

    _/_⊩¹_≡_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (A B : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ A ≡ B / Uᵣ UA = Γ / lε ⊩¹U≡ B
    Γ / lε ⊩¹ A ≡ B / ℕᵣ D = Γ / lε ⊩ℕ A ≡ B
    Γ / lε ⊩¹ A ≡ B / Emptyᵣ D = Γ / lε ⊩Empty A ≡ B
    Γ / lε ⊩¹ A ≡ B / Unitᵣ D = Γ / lε ⊩Unit A ≡ B
    Γ / lε ⊩¹ A ≡ B / ne neA = Γ / lε ⊩ne A ≡ B / neA
    Γ / lε ⊩¹ A ≡ B / Bᵣ W BA = Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / BA
    Γ / lε ⊩¹ A ≡ B / emb j< [A] = Γ / lε ⊩ A ≡ B / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t A : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ t ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / lε ⊩¹U t ∷U/ j<
    Γ / lε ⊩¹ t ∷ A / ℕᵣ D = Γ / lε ⊩ℕ t ∷ℕ
    Γ / lε ⊩¹ t ∷ A / Emptyᵣ D = Γ / lε ⊩Empty t ∷Empty
    Γ / lε ⊩¹ t ∷ A / Unitᵣ D = Γ / lε ⊩Unit t ∷Unit
    Γ / lε ⊩¹ t ∷ A / ne neA = Γ / lε ⊩ne t ∷ A / neA
    Γ / lε ⊩¹ t ∷ A / Bᵣ BΠ ΠA  = Γ / lε ⊩¹Π t ∷ A / ΠA
    Γ / lε ⊩¹ t ∷ A / Bᵣ BΣ ΣA  = Γ / lε ⊩¹Σ t ∷ A / ΣA
    Γ / lε ⊩¹ t ∷ A / emb j< [A] = Γ / lε ⊩ t ∷ A / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_≡_∷_/_ : (Γ : Con Term ℓ) {l : LCon} (lε : ⊢ₗ l) (t u A : Term ℓ) → Γ / lε ⊩¹ A → Set
    Γ / lε ⊩¹ t ≡ u ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / lε ⊩¹U t ≡ u ∷U/ j<
    Γ / lε ⊩¹ t ≡ u ∷ A / ℕᵣ D = Γ / lε ⊩ℕ t ≡ u ∷ℕ
    Γ / lε ⊩¹ t ≡ u ∷ A / Emptyᵣ D = Γ / lε ⊩Empty t ≡ u ∷Empty
    Γ / lε ⊩¹ t ≡ u ∷ A / Unitᵣ D = Γ / lε ⊩Unit t ≡ u ∷Unit
    Γ / lε ⊩¹ t ≡ u ∷ A / ne neA = Γ / lε ⊩ne t ≡ u ∷ A / neA
    Γ / lε ⊩¹ t ≡ u ∷ A / Bᵣ BΠ ΠA = Γ / lε ⊩¹Π t ≡ u ∷ A / ΠA
    Γ / lε ⊩¹ t ≡ u ∷ A / Bᵣ BΣ ΣA  = Γ / lε ⊩¹Σ t ≡ u ∷ A / ΣA
    Γ / lε ⊩¹ t ≡ u ∷ A / emb j< [A] = Γ / lε ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec j<)

    kit : LogRelKit
    kit = Kit _/_⊩¹U _/_⊩¹B⟨_⟩_
              _/_⊩¹_ _/_⊩¹_≡_/_ _/_⊩¹_∷_/_ _/_⊩¹_≡_∷_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; emb; Uₜ; Uₜ₌)

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

