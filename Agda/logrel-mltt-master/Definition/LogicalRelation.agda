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

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _/_⊩ne_ (Γ : Con Term ℓ) (l : LCon) (A : Term ℓ) : Set where
  constructor ne
  field
    K   : Term ℓ
    D   : Γ / l ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ / l ⊢ K ~ K ∷ U

-- Neutral type equality
record _/_⊩ne_≡_/_ (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) ([A] : Γ / l ⊩ne A) : Set where
  constructor ne₌
  open _/_⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ / l ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ / l ⊢ K ~ M ∷ U

-- Neutral term in WHNF
record _/_⊩neNf_∷_ (Γ : Con Term ℓ) (l : LCon) (k A : Term ℓ) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ / l ⊢ k ∷ A
    k≡k  : Γ / l ⊢ k ~ k ∷ A

-- Neutral term
record _/_⊩ne_∷_/_ (Γ : Con Term ℓ) (l : LCon) (t A : Term ℓ) ([A] : Γ / l ⊩ne A) : Set where
  inductive
  constructor neₜ
  open _/_⊩ne_ [A]
  field
    k   : Term ℓ
    d   : Γ / l ⊢ t :⇒*: k ∷ K
    nf  : Γ / l ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _/_⊩neNf_≡_∷_ (Γ : Con Term ℓ) (l : LCon) (k m A : Term ℓ) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ / l ⊢ k ~ m ∷ A

-- Neutral term equality
record _/_⊩ne_≡_∷_/_ (Γ : Con Term ℓ) (l : LCon) (t u A : Term ℓ) ([A] : Γ / l ⊩ne A) : Set where
  constructor neₜ₌
  open _/_⊩ne_ [A]
  field
    k m : Term ℓ
    d   : Γ / l ⊢ t :⇒*: k ∷ K
    d′  : Γ / l ⊢ u :⇒*: m ∷ K
    nf  : Γ / l ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_/_⊩ℕ_ : (Γ : Con Term ℓ) (l : LCon) (A : Term ℓ) → Set
Γ / l ⊩ℕ A = Γ / l ⊢ A :⇒*: ℕ

-- Natural number type equality
_/_⊩ℕ_≡_ : (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) → Set
Γ / l ⊩ℕ A ≡ B = Γ / l ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  record _/_⊩ℕ_∷ℕ (Γ : Con Term ℓ) (l : LCon) (t : Term ℓ) : Set where
    inductive
    constructor ℕₜ
    field
      n : Term ℓ
      d : Γ / l ⊢ t :⇒*: n ∷ ℕ
      n≡n : Γ / l ⊢ n ≅ n ∷ ℕ
      prop : Natural-prop Γ l n

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term ℓ) (l : LCon) : (n : Term ℓ) → Set where
    sucᵣ  : ∀ {n} → Γ / l ⊩ℕ n ∷ℕ → Natural-prop Γ l (suc n)
    zeroᵣ : Natural-prop Γ l zero
    ne    : ∀ {n} → Γ / l ⊩neNf n ∷ ℕ → Natural-prop Γ l n

mutual
  -- Natural number term equality
  record _/_⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) (l : LCon) (t u : Term ℓ) : Set where
    inductive
    constructor ℕₜ₌
    field
      k k′ : Term ℓ
      d : Γ / l ⊢ t :⇒*: k  ∷ ℕ
      d′ : Γ / l ⊢ u :⇒*: k′ ∷ ℕ
      k≡k′ : Γ / l ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ l k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : ∀ (l : LCon) (n n′ : Term ℓ) → Set where
    sucᵣ  : ∀ {l n n′} → Γ / l ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ l (suc n) (suc n′)
    zeroᵣ : ∀ {l} → [Natural]-prop Γ l zero zero
    ne    : ∀ {l n n′} → Γ / l ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ l n n′

-- Natural extraction from term WHNF property
natural : ∀ {l n} → Natural-prop Γ l n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {l a b} → [Natural]-prop Γ l a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_/_⊩Empty_ : (Γ : Con Term ℓ) (l : LCon) (A : Term ℓ) → Set
Γ / l ⊩Empty A = Γ / l ⊢ A :⇒*: Empty

-- Empty type equality
_/_⊩Empty_≡_ : (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) → Set
Γ / l ⊩Empty A ≡ B = Γ / l ⊢ B ⇒* Empty

-- WHNF property of absurd terms
data Empty-prop (Γ : Con Term ℓ) (l : LCon) : (n : Term ℓ) → Set where
  ne    : ∀ {n} → Γ / l ⊩neNf n ∷ Empty → Empty-prop Γ l n

-- Empty term
record _/_⊩Empty_∷Empty (Γ : Con Term ℓ) (l : LCon) (t : Term ℓ) : Set where
  inductive
  constructor Emptyₜ
  field
    n : Term ℓ
    d : Γ / l ⊢ t :⇒*: n ∷ Empty
    n≡n : Γ / l ⊢ n ≅ n ∷ Empty
    prop : Empty-prop Γ l n

data [Empty]-prop (Γ : Con Term ℓ) (l : LCon) : (n n′ : Term ℓ) → Set where
  ne    : ∀ {n n′} → Γ / l ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ l n n′

-- Empty term equality
record _/_⊩Empty_≡_∷Empty (Γ : Con Term ℓ) (l : LCon) (t u : Term ℓ) : Set where
  inductive
  constructor Emptyₜ₌
  field
    k k′ : Term ℓ
    d : Γ / l ⊢ t :⇒*: k  ∷ Empty
    d′ : Γ / l ⊢ u :⇒*: k′ ∷ Empty
    k≡k′ : Γ / l ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ l k k′

empty : ∀ {l n} → Empty-prop Γ l n → Neutral n
empty (ne (neNfₜ neK _ _)) = neK

esplit : ∀ {l a b} → [Empty]-prop Γ l a b → Neutral a × Neutral b
esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Reducibility of Unit

-- Unit type
_/_⊩Unit_ : (Γ : Con Term ℓ) (l : LCon) (A : Term ℓ) → Set
Γ / l ⊩Unit A = Γ / l ⊢ A :⇒*: Unit

-- Unit type equality
_/_⊩Unit_≡_ : (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) → Set
Γ / l ⊩Unit A ≡ B = Γ / l ⊢ B ⇒* Unit

record _/_⊩Unit_∷Unit (Γ : Con Term ℓ) (l : LCon) (t : Term ℓ) : Set where
  inductive
  constructor Unitₜ
  field
    n : Term ℓ
    d : Γ / l ⊢ t :⇒*: n ∷ Unit
    prop : Whnf {l} n

-- Unit term equality
record _/_⊩Unit_≡_∷Unit (Γ : Con Term ℓ) (l : LCon) (t u : Term ℓ) : Set where
  constructor Unitₜ₌
  field
    ⊢t : Γ / l ⊢ t ∷ Unit
    ⊢u : Γ / l ⊢ u ∷ Unit

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
    _/_⊩U : (Γ : Con Term ℓ) (l : LCon) → Set
    _/_⊩B⟨_⟩_ : (Γ : Con Term ℓ) (l : LCon) (W : BindingType) → Term ℓ → Set

    _/_⊩_ : (Γ : Con Term ℓ) (l : LCon) → Term ℓ → Set
    _/_⊩_≡_/_ : (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) → Γ / l ⊩ A → Set
    _/_⊩_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t A : Term ℓ) → Γ / l ⊩ A → Set
    _/_⊩_≡_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t u A : Term ℓ) → Γ / l ⊩ A → Set

module LogRel (j : TypeLevel) (rec : ∀ {j′} → j′ < j → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _/_⊩¹U (Γ : Con Term ℓ) (l : LCon) : Set where
    constructor Uᵣ
    field
      j′ : TypeLevel
      j< : j′ < j
      ⊢Γ : ⊢ Γ / l

  -- Universe type equality
  _/_⊩¹U≡_ : (Γ : Con Term ℓ) (l : LCon) (B : Term ℓ) → Set
  Γ / l ⊩¹U≡ B = B PE.≡ U -- Note lack of reduction

  -- Universe term
  record _/_⊩¹U_∷U/_ {j′} (Γ : Con Term ℓ) (l : LCon) (t : Term ℓ) (j< : j′ < j) : Set where
    constructor Uₜ
    open LogRelKit (rec j<)
    field
      A     : Term ℓ
      d     : Γ / l ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ / l ⊢ A ≅ A ∷ U
      [t]   : Γ / l ⊩ t

  -- Universe term equality
  record _/_⊩¹U_≡_∷U/_ {j′} (Γ : Con Term ℓ) (l : LCon) (t u : Term ℓ) (j< : j′ < j) : Set where
    constructor Uₜ₌
    open LogRelKit (rec j<)
    field
      A B   : Term ℓ
      d     : Γ / l ⊢ t :⇒*: A ∷ U
      d′    : Γ / l ⊢ u :⇒*: B ∷ U
      typeA : Type A
      typeB : Type B
      A≡B   : Γ / l ⊢ A ≅ B ∷ U
      [t]   : Γ / l ⊩ t
      [u]   : Γ / l ⊩ u
      [t≡u] : Γ / l ⊩ t ≡ u / [t]

  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _/_⊩¹B⟨_⟩_ (Γ : Con Term ℓ) (l : LCon) (W : BindingType) (A : Term ℓ) : Set where
      inductive
      constructor Bᵣ
      eta-equality
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ / l ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
        ⊢F : Γ / l ⊢ F
        ⊢G : Γ ∙ F / l ⊢ G
        A≡A : Γ / l ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ / l → Δ / l ⊩¹ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
            → Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ / l ⊩¹ U.wk (lift ρ) G [ a ]
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
              → ([a] : Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ / l ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / l ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ / l ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a]

    -- B-type equality
    record _/_⊩¹B⟨_⟩_≡_/_ (Γ : Con Term ℓ) (l : LCon) (W : BindingType) (A B : Term ℓ) ([A] : Γ / l ⊩¹B⟨ W ⟩ A) : Set where
      inductive
      constructor B₌
      eta-equality
      open _/_⊩¹B⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ / l ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ / l ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
               → Δ / l ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
               → ([a] : Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ / l ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _/_⊩¹Π_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) (l : LCon) (t A : Term ℓ) ([A] : Γ / l ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_∷_/_ {ℓ} Γ l t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ f → Γ / l ⊢ t :⇒*: f ∷ Π F ▹ G
            × Function f
            × Γ / l ⊢ f ≅ f ∷ Π F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
              ([a] : Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ / l ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ / l ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / l ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
              → ([a] : Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ / l ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _/_⊩¹Π_≡_∷_/_ : {ℓ : Nat} (Γ : Con Term ℓ) (l : LCon) (t u A : Term ℓ) ([A] : Γ / l ⊩¹B⟨ BΠ ⟩ A) → Set
    _/_⊩¹Π_≡_∷_/_  {ℓ} Γ l t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ f g → Γ / l ⊢ t :⇒*: f ∷ Π F ▹ G
               × Γ / l ⊢ u :⇒*: g ∷ Π F ▹ G
               × Function f
               × Function g
               × Γ / l ⊢ f ≅ g ∷ Π F ▹ G
               × Γ / l ⊩¹Π t ∷ A / [A]
               × Γ / l ⊩¹Π u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / l)
                 ([a] : Δ / l ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ / l ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _/_⊩¹Σ_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t A : Term ℓ) ([A] : Γ / l ⊩¹B⟨ BΣ ⟩ A) → Set
    Γ / l ⊩¹Σ t ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ p → Γ / l ⊢ t :⇒*: p ∷ Σ F ▹ G
            × Product p
            × Γ / l ⊢ p ≅ p ∷ Σ F ▹ G
            × (Σ (Γ / l ⊩¹ fst p ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst]
                 → Γ / l ⊩¹ snd p ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fst])

    -- Term equality of Σ-type
    _/_⊩¹Σ_≡_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t u A : Term ℓ) ([A] : Γ / l ⊩¹B⟨ BΣ ⟩ A) → Set
    Γ / l ⊩¹Σ t ≡ u ∷ A / [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ p r → Γ / l ⊢ t :⇒*: p ∷ Σ F ▹ G
               × Γ / l ⊢ u :⇒*: r ∷ Σ F ▹ G
               × Product p
               × Product r
               × Γ / l ⊢ p ≅ r ∷ Σ F ▹ G
               × Γ / l ⊩¹Σ t ∷ A / [A]
               × Γ / l ⊩¹Σ u ∷ A / [A]
               × (Σ (Γ / l ⊩¹ fst p ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
                    → Γ / l ⊩¹ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / l ⊩¹ fst p ≡ fst r ∷ U.wk id F / [F] id (wf ⊢F)
                    × Γ / l ⊩¹ snd p ≡ snd r ∷ U.wk (lift id) G [ fst p ] / [G] id (wf ⊢F) [fstp])

    -- Logical relation definition
    data _/_⊩¹_ (Γ : Con Term ℓ) : ∀ (l : LCon) → Term ℓ → Set where
      Uᵣ  : Γ / l ⊩¹U → Γ / l ⊩¹ U
      ℕᵣ  : ∀ {A} → Γ / l ⊩ℕ A → Γ / l ⊩¹ A
      Emptyᵣ : ∀ {A} → Γ / l ⊩Empty A → Γ / l ⊩¹ A
      Unitᵣ : ∀ {A} → Γ / l ⊩Unit A → Γ / l ⊩¹ A
      ne  : ∀ {A} → Γ / l ⊩ne A → Γ / l ⊩¹ A
      Bᵣ  : ∀ {A} W → Γ / l ⊩¹B⟨ W ⟩ A → Γ / l ⊩¹ A
      emb : ∀ {A j′} (j< : j′ < j) (let open LogRelKit (rec j<))
            ([A] : Γ / l ⊩ A) → Γ / l ⊩¹ A

    _/_⊩¹_≡_/_ : (Γ : Con Term ℓ) (l : LCon) (A B : Term ℓ) → Γ / l ⊩¹ A → Set
    Γ / l ⊩¹ A ≡ B / Uᵣ UA = Γ / l ⊩¹U≡ B
    Γ / l ⊩¹ A ≡ B / ℕᵣ D = Γ / l ⊩ℕ A ≡ B
    Γ / l ⊩¹ A ≡ B / Emptyᵣ D = Γ / l ⊩Empty A ≡ B
    Γ / l ⊩¹ A ≡ B / Unitᵣ D = Γ / l ⊩Unit A ≡ B
    Γ / l ⊩¹ A ≡ B / ne neA = Γ / l ⊩ne A ≡ B / neA
    Γ / l ⊩¹ A ≡ B / Bᵣ W BA = Γ / l ⊩¹B⟨ W ⟩ A ≡ B / BA
    Γ / l ⊩¹ A ≡ B / emb j< [A] = Γ / l ⊩ A ≡ B / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t A : Term ℓ) → Γ / l ⊩¹ A → Set
    Γ / l ⊩¹ t ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / l ⊩¹U t ∷U/ j<
    Γ / l ⊩¹ t ∷ A / ℕᵣ D = Γ / l ⊩ℕ t ∷ℕ
    Γ / l ⊩¹ t ∷ A / Emptyᵣ D = Γ / l ⊩Empty t ∷Empty
    Γ / l ⊩¹ t ∷ A / Unitᵣ D = Γ / l ⊩Unit t ∷Unit
    Γ / l ⊩¹ t ∷ A / ne neA = Γ / l ⊩ne t ∷ A / neA
    Γ / l ⊩¹ t ∷ A / Bᵣ BΠ ΠA  = Γ / l ⊩¹Π t ∷ A / ΠA
    Γ / l ⊩¹ t ∷ A / Bᵣ BΣ ΣA  = Γ / l ⊩¹Σ t ∷ A / ΣA
    Γ / l ⊩¹ t ∷ A / emb j< [A] = Γ / l ⊩ t ∷ A / [A]
      where open LogRelKit (rec j<)

    _/_⊩¹_≡_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (t u A : Term ℓ) → Γ / l ⊩¹ A → Set
    Γ / l ⊩¹ t ≡ u ∷ .U / Uᵣ (Uᵣ j′ j< ⊢Γ) = Γ / l ⊩¹U t ≡ u ∷U/ j<
    Γ / l ⊩¹ t ≡ u ∷ A / ℕᵣ D = Γ / l ⊩ℕ t ≡ u ∷ℕ
    Γ / l ⊩¹ t ≡ u ∷ A / Emptyᵣ D = Γ / l ⊩Empty t ≡ u ∷Empty
    Γ / l ⊩¹ t ≡ u ∷ A / Unitᵣ D = Γ / l ⊩Unit t ≡ u ∷Unit
    Γ / l ⊩¹ t ≡ u ∷ A / ne neA = Γ / l ⊩ne t ≡ u ∷ A / neA
    Γ / l ⊩¹ t ≡ u ∷ A / Bᵣ BΠ ΠA = Γ / l ⊩¹Π t ≡ u ∷ A / ΠA
    Γ / l ⊩¹ t ≡ u ∷ A / Bᵣ BΣ ΣA  = Γ / l ⊩¹Σ t ≡ u ∷ A / ΣA
    Γ / l ⊩¹ t ≡ u ∷ A / emb j< [A] = Γ / l ⊩ t ≡ u ∷ A / [A]
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

_/_⊩′⟨_⟩U : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) → Set
Γ / l ⊩′⟨ j ⟩U = Γ / l ⊩U where open LogRelKit (kit j)

_/_⊩′⟨_⟩B⟨_⟩_ : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) (W : BindingType) → Term ℓ → Set
Γ / l ⊩′⟨ j ⟩B⟨ W ⟩ A = Γ / l ⊩B⟨ W ⟩ A where open LogRelKit (kit j)

_/_⊩⟨_⟩_ : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) → Term ℓ → Set
Γ / l ⊩⟨ j ⟩ A = Γ / l ⊩ A where open LogRelKit (kit j)

_/_⊩⟨_⟩_≡_/_ : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) (A B : Term ℓ) → Γ / l ⊩⟨ j ⟩ A → Set
Γ / l ⊩⟨ j ⟩ A ≡ B / [A] = Γ / l ⊩ A ≡ B / [A] where open LogRelKit (kit j)

_/_⊩⟨_⟩_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) (t A : Term ℓ) → Γ / l ⊩⟨ j ⟩ A → Set
Γ / l ⊩⟨ j ⟩ t ∷ A / [A] = Γ / l ⊩ t ∷ A / [A] where open LogRelKit (kit j)

_/_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term ℓ) (l : LCon) (j : TypeLevel) (t u A : Term ℓ) → Γ / l ⊩⟨ j ⟩ A → Set
Γ / l ⊩⟨ j ⟩ t ≡ u ∷ A / [A] = Γ / l ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit j)

