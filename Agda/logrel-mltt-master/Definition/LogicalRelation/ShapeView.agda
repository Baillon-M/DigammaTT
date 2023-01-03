{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeView {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity

open import Tools.Nat
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.Sum as TS
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B : Term n
    l : LCon
    lε : ⊢ₗ l

-- Type for maybe embeddings of reducible types
data MaybeEmb (k : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ k ⟩ → MaybeEmb k ⊩⟨_⟩
  emb   : ∀ {k′} → k′ < k → MaybeEmb k′ ⊩⟨_⟩ → MaybeEmb k ⊩⟨_⟩

-- Specific reducible types with possible embedding

_/_⊩⟨_⟩U : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) → Set
Γ / lε ⊩⟨ k ⟩U = MaybeEmb k (λ k′ → Γ / lε ⊩′⟨ k′ ⟩U)

_/_⊩⟨_⟩ℕ_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩ℕ A = MaybeEmb k (λ k′ → Γ / lε ⊩ℕ A)

_/_⊩⟨_⟩Empty_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩Empty A = MaybeEmb k (λ k′ → Γ / lε ⊩Empty A)

_/_⊩⟨_⟩Unit_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩Unit A = MaybeEmb k (λ k′ → Γ / lε ⊩Unit A)

_/_⊩⟨_⟩ne_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩ne A = MaybeEmb k (λ k′ → Γ / lε ⊩ne A)

_/_⊩⟨_⟩B⟨_⟩_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (W : BindingType) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩B⟨ W ⟩ A = MaybeEmb k (λ k′ → Γ / lε ⊩′⟨ k′ ⟩B⟨ W ⟩ A)

-- Construct a general reducible type from a specific

U-intr : ∀ {k} → Γ / lε ⊩⟨ k ⟩U → Γ / lε ⊩⟨ k ⟩ U
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩ℕ A → Γ / lε ⊩⟨ k ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

Empty-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩Empty A → Γ / lε ⊩⟨ k ⟩ A
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

Unit-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩Unit A → Γ / lε ⊩⟨ k ⟩ A
Unit-intr (noemb x) = Unitᵣ x
Unit-intr (emb 0<1 x) = emb 0<1 (Unit-intr x)

ne-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩ne A → Γ / lε ⊩⟨ k ⟩ A
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

B-intr : ∀ {A k} W → Γ / lε ⊩⟨ k ⟩B⟨ W ⟩ A → Γ / lε ⊩⟨ k ⟩ A
B-intr W (noemb x) = Bᵣ W x
B-intr W (emb 0<1 x) = emb 0<1 (B-intr W x)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ U → Γ / lε ⊩⟨ k ⟩U
U-elim (Uᵣ′ k′ k< ⊢Γ) = noemb (Uᵣ k′ k< ⊢Γ)
U-elim (ℕᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Emptyᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (Unitᵣ D) with whnfRed* (red D) Uₙ
... | ()
U-elim (ne′ K D neK K≡K) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁
U-elim (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (U≢αne αB (whnfRed* (red A⇒B) Uₙ))

ℕ-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* ℕ → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩ℕ A
ℕ-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
... | ()
ℕ-elim′ D (Unitᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
... | ()
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂
ℕ-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (ℕ≢αne αB (whrDet* (D , ℕₙ) (red A⇒B , αₙ αB)))

ℕ-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ ℕ → Γ / lε ⊩⟨ k ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* Empty → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩Empty A
Empty-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)
... | ()
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (Unitᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , Unitₙ)
... | ()
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , ℕₙ)
... | ()
Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Empty-elim′ D (emb 0<1 x) | emb () x₂
Empty-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (Empty≢αne αB (whrDet* (D , Emptyₙ) (red A⇒B , αₙ αB)))

Empty-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ Empty → Γ / lε ⊩⟨ k ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

Unit-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* Unit → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩Unit A
Unit-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Unitₙ)
... | ()
Unit-elim′ D (Unitᵣ D′) = noemb D′
Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
... | ()
Unit-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
Unit-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
... | ()
Unit-elim′ D (emb 0<1 x) with Unit-elim′ D x
Unit-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Unit-elim′ D (emb 0<1 x) | emb () x₂
Unit-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (Unit≢αne αB (whrDet* (D , Unitₙ) (red A⇒B , αₙ αB)))

Unit-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ Unit → Γ / lε ⊩⟨ k ⟩Unit Unit
Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A k K} → Γ / lε ⊢ A ⇒* K → Neutral K → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩ne A
ne-elim′ D neK (Uᵣ′ k′ k< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (Unitᵣ D′) = ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (B≢ne W neK (whrDet* (red D′ , ⟦ W ⟧ₙ) (D , ne neK)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂
ne-elim′ D neK (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (ne≢αne neK αB (whrDet* (D , ne neK) (red A⇒B , αₙ αB)))

ne-elim : ∀ {k K} → Neutral K  → Γ / lε ⊩⟨ k ⟩ K → Γ / lε ⊩⟨ k ⟩ne K
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

B-elim′ : ∀ {A F G k} W → Γ / lε ⊢ A ⇒* ⟦ W ⟧ F ▹ G → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩B⟨ W ⟩ A
B-elim′ W D (Uᵣ′ k′ k< ⊢Γ) =
  ⊥-elim (U≢B W (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ℕᵣ D′) =
  ⊥-elim (ℕ≢B W (whrDet* (red D′ , ℕₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Emptyᵣ D′) =
  ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (Unitᵣ D′) =
  ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
B-elim′ W D (ne′ K D′ neK K≡K) =
  ⊥-elim (B≢ne W neK (whrDet* (D , ⟦ W ⟧ₙ) (red D′ , ne neK)))
B-elim′ BΠ D (Bᵣ′ BΣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Πₙ) (red D′ , Σₙ)
... | ()
B-elim′ BΣ D (Bᵣ′ BΠ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) with whrDet* (D , Σₙ) (red D′ , Πₙ)
... | ()
B-elim′ BΠ D (Bᵣ′ BΠ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Bᵣ F G D′ ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
B-elim′ BΣ D (Bᵣ′ BΣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Bᵣ F G D′ ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
B-elim′ W D (emb 0<1 x) with B-elim′ W D x
B-elim′ W D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
B-elim′ W D (emb 0<1 x) | emb () x₂
B-elim′ BΣ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (B≢αne BΣ αB (whrDet* (D , Σₙ) (red A⇒B , αₙ αB)))
B-elim′ BΠ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (B≢αne BΠ αB (whrDet* (D , Πₙ) (red A⇒B , αₙ αB)))

B-elim : ∀ {F G k} W → Γ / lε ⊩⟨ k ⟩ ⟦ W ⟧ F ▹ G → Γ / lε ⊩⟨ k ⟩B⟨ W ⟩ ⟦ W ⟧ F ▹ G
B-elim W [Π] = B-elim′ W (id (escape [Π])) [Π]

Π-elim : ∀ {F G k} → Γ / lε ⊩⟨ k ⟩ Π F ▹ G → Γ / lε ⊩⟨ k ⟩B⟨ BΠ ⟩ Π F ▹ G
Π-elim [Π] = B-elim′ BΠ (id (escape [Π])) [Π]

Σ-elim : ∀ {F G k} → Γ / lε ⊩⟨ k ⟩ Σ F ▹ G → Γ / lε ⊩⟨ k ⟩B⟨ BΣ ⟩ Σ F ▹ G
Σ-elim [Σ] = B-elim′ BΣ (id (escape [Σ])) [Σ]

ℕ≠U : ∀ {k k'} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩′⟨ k' ⟩U)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ U / ℕᵣ [A]) → ⊥
ℕ≠U [A] [B] (⊩ℕ≡ _ _ A⇒N) with whnfRed* (A⇒N) Uₙ
... | ()
ℕ≠U {k = k} {k' = k'} [A] [B] (ϝ⊩ℕ≡ mε A⇒B αB tA fA) = U≢αne αB (whrDet* (id (⊢A-red A⇒B) , Uₙ) (red A⇒B , αₙ αB))

ℕ≠Unit : ∀ {k} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩Unit B)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ B / ℕᵣ [A]) → ⊥
ℕ≠Unit [A] [B] (⊩ℕ≡ _ _ A⇒N) with whrDet* ( red [B] , Unitₙ ) ( A⇒N , ℕₙ )
... | ()
ℕ≠Unit {k = k} [A] [B] (ϝ⊩ℕ≡ mε A⇒B αB tA fA) = Unit≢αne αB (whrDet* (red [B] , Unitₙ) (red A⇒B , αₙ αB))

ℕ≠Empty : ∀ {k} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩Empty B)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ B / ℕᵣ [A]) → ⊥
ℕ≠Empty [A] [B] (⊩ℕ≡ _ _ A⇒N) with whrDet* ( red [B] , Emptyₙ ) ( A⇒N , ℕₙ )
... | ()
ℕ≠Empty {k = k} [A] [B] (ϝ⊩ℕ≡ mε A⇒B αB tA fA) = Empty≢αne αB (whrDet* (red [B] , Emptyₙ) (red A⇒B , αₙ αB))

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {k ⊩⟨_⟩} → MaybeEmb k ⊩⟨_⟩ → ∃ λ k′ → ⊩⟨ k′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView (Γ : Con Term n) : ∀ {l : LCon} {lε : ⊢ₗ l} k k′ A B (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ B) → Set where
  Uᵥ : ∀ {l lε k k′} UA UB → ShapeView Γ {l} {lε} k k′ U U (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {l} {lε} {A B k k′} ℕA ℕB → ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {l} {lε} {A B k k′} EmptyA EmptyB → ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  Unitᵥ : ∀ {l} {lε} {A B k k′} UnitA UnitB → ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
  ne  : ∀ {l} {lε} {A B k k′} neA neB
      → ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB)
  Bᵥ : ∀ {l} {lε} {A B k k′} W BA BB
    → ShapeView Γ {l} {lε} k k′ A B (Bᵣ W BA) (Bᵣ W BB)
  ϝᵣ-l : ∀ {l lε n nε} {k k' A A' B} A⇒A' αA [B] [A]t [A]f [B]t [B]f
       → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A' B [A]t [B]t
       → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A' B [A]f [B]f
       → ShapeView Γ {l} {lε} k k' A B (ϝᵣ nε A⇒A' αA [A]t [A]f) [B]
  ϝᵣ-r : ∀ {l lε n nε} {k k' A B B'} B⇒B' αB [A] [A]t [A]f [B]t [B]f
       → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A B' [A]t [B]t
       → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A B' [A]f [B]f
       → ShapeView Γ {l} {lε} k k' A B [A] (ϝᵣ nε B⇒B' αB [B]t [B]f)
  emb⁰¹ : ∀ {l} {lε} {A B k p q}
        → ShapeView Γ {l} {lε} ⁰ k A B p q
        → ShapeView Γ {l} {lε} ¹ k A B (emb 0<1 p) q
  emb¹⁰ : ∀ {l} {lε} {A B k p q}
        → ShapeView Γ {l} {lε} k ⁰ A B p q
        → ShapeView Γ {l} {lε} k ¹ A B p (emb 0<1 q)

RedShapeView : ∀ {A A' B B' k k' k'' k'''} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k' ⟩ B}
                                      ([AB] : ShapeView Γ k k' A B [A] [B])
                                      ([A]' : Γ / lε ⊩⟨ k'' ⟩ A') ([B]' : Γ / lε ⊩⟨ k''' ⟩ B')
                                      (A⇒A' : Γ / lε ⊢ A :⇒*: A') (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                                      → ShapeView Γ k'' k''' A' B' [A]' [B]'

-- The case of U
RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
  with whnfRed* (red A⇒U) Uₙ with whnfRed* (red B⇒U) Uₙ
RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
  | PE.refl | PE.refl with TyLogU [A]' with TyLogU [B]' 
RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
  | PE.refl | PE.refl | UA' , PE.refl | UB' , PE.refl = Uᵥ UA' UB'

-- Diagonal cases
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ℕᵣ ℕB) A⇒A'' B⇒B'' = ℕᵥ ℕA ℕB
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A⇒A'' B⇒B'' = Emptyᵥ EmptyA EmptyB
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Unitᵣ UnitB) A⇒A'' B⇒B'' = Unitᵥ UnitA UnitB
RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
  Bᵥ BΠ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
  Bᵥ BΣ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
RedShapeView (ne neA neB) (ne neA') (ne neB') A⇒A'' B⇒B'' = ne neA' neB'
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
  with whrDet* (red A⇒A' , αₙ αA) (⇒*-comp (red A⇒A′) (red A⇒A'') , αₙ αA')
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
  | PE.refl with αNeutralHProp αA αA'
RedShapeView (ϝᵣ-l {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
  | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
  | PE.refl | PE.refl | PE.refl =
  ϝᵣ-l A⇒A'' αA' [B'] tA fA _ _
    (RedShapeView tAB tA (τTyLog [B']) (idRed:*: (τTy _ _ _ _ (⊢B-red A⇒A''))) (τwfRed* B⇒B''))
    (RedShapeView fAB fA (τTyLog [B']) (idRed:*: (τTy _ _ _ _ (⊢B-red A⇒A''))) (τwfRed* B⇒B''))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
  with whrDet* (red B⇒B' , αₙ αB) (⇒*-comp (red B⇒B′) (red B⇒B'') , αₙ αB')
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
  | PE.refl with αNeutralHProp αB αB'
RedShapeView (ϝᵣ-r {nε = nε} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
  | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
  | PE.refl | PE.refl | PE.refl =
  ϝᵣ-r B⇒B'' αB' [A'] _ _ tB fB
    (RedShapeView tAB (τTyLog [A']) tB (τwfRed* A⇒A'') (idRed:*: (τTy _ _ _ _ (⊢B-red B⇒B''))))
    (RedShapeView fAB (τTyLog [A']) fB (τwfRed* A⇒A'') (idRed:*: (τTy _ _ _ _ (⊢B-red B⇒B''))))

-- Embeddings
RedShapeView (emb⁰¹ [AB]) = RedShapeView [AB]
RedShapeView (emb¹⁰ [AB]) = RedShapeView [AB]
RedShapeView [AB] (emb 0<1 [A]) [B] A⇒A'' B⇒B′ = emb⁰¹ (RedShapeView [AB] [A] [B] A⇒A'' B⇒B′)
RedShapeView [AB] [A] (emb 0<1 [B]) A⇒A'' B⇒B′ = emb¹⁰ (RedShapeView [AB] [A] [B] A⇒A'' B⇒B′)


-- ℕ
RedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
  with whrDet* (red A⇒A'' , Uₙ) (red ℕA' , ℕₙ)
RedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
  | ()
RedShapeView (ℕᵥ ℕA' ℕB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' 
  with whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red ℕA' , ℕₙ)
... | ()
RedShapeView (ℕᵥ ℕA' ℕB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red ℕA' , ℕₙ)
... | ()
RedShapeView (ℕᵥ ℕA' ℕB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕA' , ℕₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
RedShapeView (ℕᵥ ℕA' ℕB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' = 
  ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕA') , ℕₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
RedShapeView (ℕᵥ ℕA' ℕB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕA' , ℕₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
  with whrDet* (red B⇒B'' , Uₙ) (red ℕB' , ℕₙ)
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
  | ()
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Emptyᵣ D) A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red B⇒B'') (red D) , Emptyₙ) (red ℕB' , ℕₙ)
... | ()
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Unitᵣ D) A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red B⇒B'') (red D) , Unitₙ) (red ℕB' , ℕₙ)
... | ()
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = 
  ⊥-elim (ℕ≢B W (whrDet* (red ℕB' , ℕₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' = 
  ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕB') , ℕₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = 
  ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕB' , ℕₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))

-- Empty
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
  with whrDet* (red A⇒A'' , Uₙ) (red EmptyA' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' 
  with whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red EmptyA' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red EmptyA' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
 ⊥-elim (Empty≢B W (whrDet* (red EmptyA' , Emptyₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
RedShapeView (Emptyᵥ EmptyA' EmptyB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyA') , Emptyₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
RedShapeView (Emptyᵥ EmptyA' EmptyB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' = 
  ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyA' , Emptyₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Uᵣ UB) A⇒A'' B⇒B''
  with whrDet* (red B⇒B'' , Uₙ) (red EmptyB' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ℕᵣ ℕB) A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red EmptyB' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Unitᵣ UnitB) A⇒A'' B⇒B''
  with whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red EmptyB' , Emptyₙ)
... | ()
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyB' , Emptyₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyB') , Emptyₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyB' , Emptyₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- Unit
RedShapeView (Unitᵥ UnitA' UnitB')  (Uᵣ UA) [B'] A⇒A'' B⇒B''
  with whrDet* (red A⇒A'' , Uₙ) (red UnitA' , Unitₙ)
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B''
  with whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) 
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B''
  with whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) 
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' = 
 ⊥-elim (Unit≢B W (whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
RedShapeView (Unitᵥ UnitA' UnitB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢ne neK (whrDet* ((red UnitA') , Unitₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
RedShapeView (Unitᵥ UnitA' UnitB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢αne αA' (whrDet* (red UnitA' , Unitₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Uᵣ UB) A⇒A'' B⇒B''
  with whrDet* (red B⇒B'' , Uₙ) (red UnitB' , Unitₙ)
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ℕᵣ ℕB) A⇒A'' B⇒B''
  with whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) 
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Emptyᵣ D) A⇒A'' B⇒B'' 
  with whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , Emptyₙ) 
... | ()
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
 ⊥-elim (Unit≢B W (whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢ne neK (whrDet* ((red UnitB') , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢αne αA' (whrDet* (red UnitB' , Unitₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- Σ and Π-types
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (U≢B W (whrDet* (red A⇒A'' , Uₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A] (Uᵣ UB) A⇒A'' B⇒B'' =
  ⊥-elim (U≢B W (whrDet* (red B⇒B'' , Uₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' = 
 ⊥-elim (ℕ≢B W (whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
 ⊥-elim (Empty≢B W (whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
 ⊥-elim (Unit≢B W (whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ne′ K' D' neK' K≡K') [B'] A⇒A'' B⇒B'' =
  ⊥-elim (B≢ne W neK' (whrDet* ((red D) , ⟦ W ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ne neK')))
RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))
RedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' 
             with whrDet* (red D , ⟦ BΠ ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ BΣ ⟧ₙ)
RedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
             | ()
RedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
             with whrDet* (red D , ⟦ BΣ ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ BΠ ⟧ₙ)
RedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
             | ()


RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
 ⊥-elim (ℕ≢B W (whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
 ⊥-elim (Empty≢B W (whrDet* (⇒*-comp (red B⇒B'') (red EmptyB) , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
 ⊥-elim (Unit≢B W (whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red D , ⟦ W ⟧ₙ)))
RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
             with whrDet* (red D , ⟦ BΣ ⟧ₙ) (⇒*-comp (red B⇒B'') (red D'') , ⟦ BΠ ⟧ₙ)
RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
             | ()
RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
             with whrDet* (red D , ⟦ BΠ ⟧ₙ) (⇒*-comp (red B⇒B'') (red D'') , ⟦ BΣ ⟧ₙ)
RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
             | ()
RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
  ⊥-elim (B≢ne W neK (whrDet* ((red D) , ⟦ W ⟧ₙ) (⇒*-comp (red B⇒B'') (red D₁) , ne neK)))
RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
  ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- Neutrals
RedShapeView (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
  with whrDet* (red A⇒A'' , Uₙ) (red D , ne neK)
RedShapeView (ne (ne K D () K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
  | PE.refl 
RedShapeView (ne (ne K D neK K≡K) neB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red D , ne neK)))
RedShapeView (ne (ne K D neK K≡K) neB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red D , ne neK)))
RedShapeView (ne (ne K D neK K≡K) neB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red D , ne neK)))
RedShapeView (ne (ne K D neK K≡K) neB) (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
  ⊥-elim (B≢ne W neK (whrDet* (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ) (red D , ne neK)))
RedShapeView (ne (ne K D neK K≡K) neB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
  with whrDet* (red B⇒B'' , Uₙ) (red D , ne neK)
RedShapeView (ne neA (ne K D () K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
  | PE.refl 
RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red D , ne neK)))
RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red EmptyB) , Emptyₙ) (red D , ne neK)))
RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red D , ne neK)))
RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Bᵣ′ W F G D'' ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
  ⊥-elim (B≢ne W neK (whrDet* (⇒*-comp (red B⇒B'') (red D'') , ⟦ W ⟧ₙ) (red D , ne neK)))
RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
  ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) (⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))

-- αNeutrals
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (U≢αne αA (whrDet* (red A⇒A'' , Uₙ) (red A⇒A' , αₙ αA)))
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢αne αA (whrDet* (red ℕA , ℕₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵣ D) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢αne αA (whrDet* (red D , Emptyₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵣ D) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢αne αA (whrDet* (red D , Unitₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne′ K D₁ neK K≡K) [B'] A⇒A'' B⇒B'' =
  ⊥-elim (ne≢αne neK αA (whrDet* (red D₁ , ne neK) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))

RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Uᵣ UB) A⇒A'' B⇒B'' =
  ⊥-elim (U≢αne αB (whrDet* (red B⇒B'' , Uₙ) (red B⇒B' , αₙ αB)))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ℕᵣ ℕB) A⇒A'' B⇒B'' =
  ⊥-elim (ℕ≢αne αB (whrDet* (red ℕB , ℕₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Emptyᵣ D) A⇒A'' B⇒B'' =
  ⊥-elim (Empty≢αne αB (whrDet* (red D , Emptyₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Unitᵣ D) A⇒A'' B⇒B'' =
  ⊥-elim (Unit≢αne αB (whrDet* (red D , Unitₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
  ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
  ⊥-elim (ne≢αne neK αB (whrDet* (red D₁ , ne neK) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))



AntiRedShapeView : ∀ {A A' B B' k k' k'' k'''} {[A]' : Γ / lε ⊩⟨ k ⟩ A'} {[B]' : Γ / lε ⊩⟨ k' ⟩ B'}
                                      ([AB]' : ShapeView Γ k k' A' B' [A]' [B]')
                                      ([A] : Γ / lε ⊩⟨ k'' ⟩ A) ([B] : Γ / lε ⊩⟨ k''' ⟩ B)
                                      (A⇒A' : Γ / lε ⊢ A :⇒*: A') (B⇒B' : Γ / lε ⊢ B :⇒*: B')
                                      → ShapeView Γ k'' k''' A B [A] [B]
AntiRedShapeView [AB]' [A] [B] A⇒A' B⇒B' = {!!}


LogW0 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
       ([A] : Γ / lε' ⊩⟨ ⁰ ⟩ A) (f< : l ≤ₗ l')
       → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA'))
LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = (BA' , PE.refl)
LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = (BA' , PE.refl)
LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
  with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
... | ()
LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
  with (whrDet* ( red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
... | ()
LogW0 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
  ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
  ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
  ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
  ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
  ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb () [A]) 
LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
  ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))


LogW1 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
       ([A] : Γ / lε' ⊩⟨ ¹ ⟩ A) (f< : l ≤ₗ l')
       → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA')) TS.⊎ (∃ (λ BA' → [A] PE.≡ emb 0<1 (Bᵣ W BA')))
LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = TS.inj₁ (BA' , PE.refl)
LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = TS.inj₁ (BA' , PE.refl)
LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
  with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
... | ()
LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
  with (whrDet* (red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
... | ()
LogW1 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
  ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
  ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
  ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
  ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
  ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
LogW1 W BA (emb 0<1 [A]) f< with LogW0 W BA [A] f<
LogW1 W BA (emb 0<1 [A]) f< | BA' , PE.refl = TS.inj₂ (BA' , PE.refl)
LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
  ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))


ShapeView≤W : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
                      {WA WB} {BA : Γ / lε ⊩′⟨ k ⟩B⟨ WA ⟩ A}  {BB : Γ / lε ⊩′⟨ k′ ⟩B⟨ WB ⟩ B}
                      ([AB] : ShapeView Γ k k′ A B (Bᵣ WA BA) (Bᵣ WB BB))
                      ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
                      (≤ε : l ≤ₗ l')
                      → ShapeView Γ j j' A B [A]' [B]'
ShapeView≤W [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤W [AB] [A] [B] f<)
ShapeView≤W [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤W [AB] [A] [B] f<)

-- Diagonal cases
ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') f< =
  Bᵥ BΠ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') f< =
  Bᵥ BΣ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'')
-- Σ and Π-types
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Uᵣ UA) [B'] f< =
  ⊥-elim (U≢B W (whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A] (Uᵣ UB) f< =
  ⊥-elim (U≢B W (whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ℕᵣ ℕA) [B'] f< = 
 ⊥-elim (ℕ≢B W (whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Emptyᵣ EmptyA) [B'] f< =
 ⊥-elim (Empty≢B W (whrDet* ( (red EmptyA) , Emptyₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Unitᵣ UnitA) [B'] f< =
 ⊥-elim (Unit≢B W (whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ne′ K' D' neK' K≡K') [B'] f< =
  ⊥-elim (B≢ne W neK' (whrDet* ((red (wfRed≤* f< D) ) , ⟦ W ⟧ₙ) ( (red D') , ne neK')))
ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
  ⊥-elim (B≢αne W αA' (whrDet* (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ) (  (red A⇒A') , αₙ αA')))
ShapeView≤W (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<  
             with whrDet* (red (wfRed≤* f< D)  , ⟦ BΠ ⟧ₙ) ( (red D') , ⟦ BΣ ⟧ₙ)
ShapeView≤W (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
             | ()
ShapeView≤W (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
             with whrDet* (red (wfRed≤* f< D)  , ⟦ BΣ ⟧ₙ) ( (red D') , ⟦ BΠ ⟧ₙ)
ShapeView≤W (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
             (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
             | ()
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ℕᵣ ℕB) f< =
 ⊥-elim (ℕ≢B W (whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Emptyᵣ EmptyB) f< =
 ⊥-elim (Empty≢B W (whrDet* ( (red EmptyB) , Emptyₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Unitᵣ UnitB) f< =
 ⊥-elim (Unit≢B W (whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f< 
             with whrDet* (red (wfRed≤* f< D)  , ⟦ BΣ ⟧ₙ) ( (red D'') , ⟦ BΠ ⟧ₙ)
ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
             (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
             | ()
ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
             with whrDet* (red (wfRed≤* f< D)  , ⟦ BΠ ⟧ₙ) ( (red D'') , ⟦ BΣ ⟧ₙ)
ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
             (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
             | ()
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ne′ K D₁ neK K≡K) f< =
  ⊥-elim (B≢ne W neK (whrDet* ((red (wfRed≤* f< D) ) , ⟦ W ⟧ₙ) ( (red D₁) , ne neK)))
ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ϝᵣ mε A⇒A' αA' tA fA) f< =
  ⊥-elim (B≢αne W αA' (whrDet* (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ) (  (red A⇒A') , αₙ αA')))

ShapeView≤ne : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
                      {neA neB}
                      ([AB] : ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB))
                      ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
                      (≤ε : l ≤ₗ l')
                      → ShapeView Γ j j' A B [A]' [B]'
-- Diagonal case
ShapeView≤ne (ne neA neB) (ne neA') (ne neB') f< = ne neA' neB'
-- Embeddings
ShapeView≤ne [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ne [AB] [A] [B] f<)
ShapeView≤ne [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ne [AB] [A] [B] f<)
-- Impossible cases
ShapeView≤ne (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< D)  , ne neK)
ShapeView≤ne (ne (ne K D () K≡K) neB) (Uᵣ UA) [B'] f<
  | PE.refl 
ShapeView≤ne (ne (ne K D neK K≡K) neB) (ℕᵣ ℕA) [B'] f< =
  ⊥-elim (ℕ≢ne neK (whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne (ne K D neK K≡K) neB) (Emptyᵣ EmptyA) [B'] f< =
  ⊥-elim (Empty≢ne neK (whrDet* ( (red EmptyA) , Emptyₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne (ne K D neK K≡K) neB) (Unitᵣ UnitA) [B'] f< =
  ⊥-elim (Unit≢ne neK (whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne (ne K D neK K≡K) neB) (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
  ⊥-elim (B≢ne W neK (whrDet* ( (red D') , ⟦ W ⟧ₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne (ne K D neK K≡K) neB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
  ⊥-elim (ne≢αne neK αA' (whrDet* (red (wfRed≤* f< D)  , ne neK) ( (red A⇒A') , αₙ αA')))

ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) f< 
  with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< D)  , ne neK)
ShapeView≤ne (ne neA (ne K D () K≡K)) (ne neA') (Uᵣ UB) f<
  | PE.refl 
ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (ℕᵣ ℕB) f< =
  ⊥-elim (ℕ≢ne neK (whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Emptyᵣ EmptyB) f< =
  ⊥-elim (Empty≢ne neK (whrDet* ( (red EmptyB) , Emptyₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Unitᵣ UnitB) f< =
  ⊥-elim (Unit≢ne neK (whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Bᵣ′ W F G D'' ⊢F ⊢G A≡A [F] [G] G-ext) f< =
  ⊥-elim (B≢ne W neK (whrDet* ( (red D'') , ⟦ W ⟧ₙ) (red (wfRed≤* f< D)  , ne neK)))
ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (ϝᵣ mε A⇒A' αA' tA fA) f< =
  ⊥-elim (ne≢αne neK αA' (whrDet* (red (wfRed≤* f< D)  , ne neK) ( (red A⇒A') , αₙ αA')))

ShapeView≤ℕ : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
                      {ℕA ℕB}
                      ([AB] : ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB))
                      ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
                      (≤ε : l ≤ₗ l')
                      → ShapeView Γ j j' A B [A]' [B]'
-- Diagonal case
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ℕᵣ ℕB) f< = ℕᵥ ℕA ℕB
-- Embeddings
ShapeView≤ℕ [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ℕ [AB] [A] [B] f<)
ShapeView≤ℕ [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ℕ [AB] [A] [B] f<)
-- Impossible cases
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] f< 
  with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< ℕA') , ℕₙ)
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] f<
  | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Emptyᵣ EmptyA) [B'] f<
  with whrDet* ( red EmptyA , Emptyₙ) (red (wfRed≤* f< ℕA') , ℕₙ)
... | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Unitᵣ UnitA) [B'] f<
  with whrDet* ( (red UnitA) , Unitₙ) (red ( wfRed≤* f< ℕA') , ℕₙ)
... | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
  ⊥-elim (ℕ≢B W (whrDet* (red (wfRed≤* f< ℕA') , ℕₙ) ( (red D') , ⟦ W ⟧ₙ)))
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ne′ K D neK K≡K) [B'] f< = 
  ⊥-elim (ℕ≢ne neK (whrDet* ((red (wfRed≤* f< ℕA') ) , ℕₙ) ( (red D) , ne neK)))
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
  ⊥-elim (ℕ≢αne αA' (whrDet* (red (wfRed≤* f< ℕA')  , ℕₙ) (  (red A⇒A') , αₙ αA')))

ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB)  f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) f<
  | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Emptyᵣ D) f< 
  with whrDet* ( (red D) , Emptyₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
... | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Unitᵣ D) f<
  with whrDet* ( (red D) , Unitₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
... | ()
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< = 
  ⊥-elim (ℕ≢B W (whrDet* (red (wfRed≤* f< ℕB')  , ℕₙ) ( (red D) , ⟦ W ⟧ₙ)))
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ne′ K D neK K≡K) f< = 
  ⊥-elim (ℕ≢ne neK (whrDet* ((red (wfRed≤* f< ℕB') ) , ℕₙ) ( (red D) , ne neK)))
ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ϝᵣ mε A⇒A' αA' tA fA) f< = 
  ⊥-elim (ℕ≢αne αA' (whrDet* (red (wfRed≤* f< ℕB')  , ℕₙ) (  (red A⇒A') , αₙ αA')))


ShapeView≤Empty : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
                      {EmptyA EmptyB}
                      ([AB] : ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB))
                      ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
                      (≤ε : l ≤ₗ l')
                      → ShapeView Γ j j' A B [A]' [B]'
-- Diagonal case
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) f< = Emptyᵥ EmptyA EmptyB
-- Embeddings
ShapeView≤Empty [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤Empty [AB] [A] [B] f<)
ShapeView≤Empty [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤Empty [AB] [A] [B] f<)
-- Impossible cases
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Uᵣ UA) [B'] f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ℕᵣ ℕA) [B'] f<
  with whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Unitᵣ UnitA) [B'] f< 
  with whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
 ⊥-elim (Empty≢B W (whrDet* (red (wfRed≤* f< EmptyA')  , Emptyₙ) ( (red D') , ⟦ W ⟧ₙ)))
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ne′ K D neK K≡K) [B'] f< =
  ⊥-elim (Empty≢ne neK (whrDet* ((red (wfRed≤* f< EmptyA') ) , Emptyₙ) ( (red D) , ne neK)))
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< = 
  ⊥-elim (Empty≢αne αA' (whrDet* (red (wfRed≤* f< EmptyA')  , Emptyₙ) (  (red A⇒A') , αₙ αA')))

ShapeView≤Empty {lε' = lε'} (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Uᵣ UB) f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ℕᵣ ℕB) f<
  with whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Unitᵣ UnitB) f<
  with whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
... | ()
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< =
  ⊥-elim (Empty≢B W (whrDet* (red (wfRed≤* f< EmptyB')  , Emptyₙ) ( (red D) , ⟦ W ⟧ₙ)))
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ne′ K D neK K≡K) f< =
  ⊥-elim (Empty≢ne neK (whrDet* ((red (wfRed≤* f< EmptyB') ) , Emptyₙ) ( (red D) , ne neK)))
ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ϝᵣ mε A⇒A' αA' tA fA) f< =
  ⊥-elim (Empty≢αne αA' (whrDet* (red (wfRed≤* f< EmptyB')  , Emptyₙ) (  (red A⇒A') , αₙ αA')))


ShapeView≤ : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
                      {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
                      ([AB] : ShapeView Γ k k′ A B [A] [B])
                      ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
                      (≤ε : l ≤ₗ l')
                      → ShapeView Γ j j' A B [A]' [B]'

ShapeView≤ (Uᵥ UA UB) [A'] [B'] f<
  with TyLogU [A'] with TyLogU [B']
ShapeView≤ (Uᵥ UA UB) (Uᵣ UA') (Uᵣ UB') f<
  | UA' , PE.refl | UB' , PE.refl = Uᵥ UA' UB'

-- Diagonal cases
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Unitᵣ UnitB) f< = Unitᵥ UnitA UnitB

-- Embeddings
ShapeView≤ (emb⁰¹ [AB]) [A'] [B'] f< = ShapeView≤ [AB] [A'] [B'] f<
ShapeView≤ (emb¹⁰ [AB]) [A'] [B'] f< = ShapeView≤ [AB] [A'] [B'] f<
ShapeView≤ [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ [AB] [A] [B] f<)
ShapeView≤ [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ [AB] [A] [B] f<)


-- ℕ
ShapeView≤ {k = k} {k′ = k′} (ℕᵥ ℕA' ℕB') [A'] [B'] f< =
  ShapeView≤ℕ {_} {_} {_} {_} {k} {k′} (ℕᵥ ℕA' ℕB') [A'] [B'] f<

-- Empty
ShapeView≤ {k = k} {k′ = k′} (Emptyᵥ EmptyA' EmptyB') [A'] [B'] f<
  = ShapeView≤Empty {_} {_} {_} {_} {k = k} {k′ = k′} (Emptyᵥ EmptyA' EmptyB') [A'] [B'] f<

-- Unit
ShapeView≤ (Unitᵥ UnitA' UnitB')  (Uᵣ UA) [B']  f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< UnitA')  , Unitₙ)
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (ℕᵣ ℕA) [B'] f<
  with whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red ℕA) , ℕₙ) 
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (Emptyᵣ EmptyA) [B'] f<
  with whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red EmptyA) , Emptyₙ) 
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< = 
 ⊥-elim (Unit≢B W (whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red D') , ⟦ W ⟧ₙ)))
ShapeView≤ (Unitᵥ UnitA' UnitB') (ne′ K D neK K≡K) [B'] f< =
  ⊥-elim (Unit≢ne neK (whrDet* ((red (wfRed≤* f< UnitA') ) , Unitₙ) ( (red D) , ne neK)))
ShapeView≤ (Unitᵥ UnitA' UnitB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
  ⊥-elim (Unit≢αne αA' (whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) (  (red A⇒A') , αₙ αA')))

ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Uᵣ UB) f<
  with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< UnitB')  , Unitₙ)
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ℕᵣ ℕB) f<
  with whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red ℕB) , ℕₙ) 
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Emptyᵣ D) f<  
  with whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red D) , Emptyₙ) 
... | ()
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< =
 ⊥-elim (Unit≢B W (whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red D) , ⟦ W ⟧ₙ)))
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ne′ K D neK K≡K) f< =
  ⊥-elim (Unit≢ne neK (whrDet* ((red (wfRed≤* f< UnitB') ) , Unitₙ) ( (red D) , ne neK)))
ShapeView≤ (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ϝᵣ mε A⇒A' αA' tA fA) f< =
  ⊥-elim (Unit≢αne αA' (whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) (  (red A⇒A') , αₙ αA')))


-- Σ and Π-types
ShapeView≤ (Bᵥ W BA BB) [A'] [B'] f< =
  ShapeView≤W (Bᵥ W BA BB) [A'] [B'] f<

-- Neutrals
ShapeView≤ {k = k} {k′ = k′} (ne neA neB) [A'] [B'] f< =
  ShapeView≤ne {_} {_} {_} {_} {k} {k′} (ne neA neB) [A'] [B'] f<

-- αNeutrals
ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  with decidInLConNat l' n
ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  | TS.inj₁ (TS.inj₁ nε') =
  AntiRedShapeView (ShapeView≤ tAB (TyLog≤ (≤ₗ-add _ _ _ f< nε') [A]t) [B'] (≤ₗ-add _ _ _ f< nε')) [A'] [B']
                   (wfRed≤* f< A⇒A') (idRed:*: (escape [B']))
ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  | TS.inj₁ (TS.inj₂ nε') =
  AntiRedShapeView (ShapeView≤ fAB (TyLog≤ (≤ₗ-add _ _ _ f< nε') [A]f) [B'] (≤ₗ-add _ _ _ f< nε')) [A'] [B']
                   (wfRed≤* f< A⇒A') (idRed:*: (escape [B']))
ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵣ ℕA) [B'] f<
  | TS.inj₂ notinl' =
  ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
                    (whrDet* (red ℕA , ℕₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵣ D) [B'] f<
  | TS.inj₂ notinl' =
  ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
                    (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵣ D) [B'] f<
  | TS.inj₂ notinl' =
  ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
                   (whrDet* (red D , Unitₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [B'] f<
  | TS.inj₂ notinl' =
  ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αA)
                    (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne′ K D₁ neK K≡K) [B'] f<
  | TS.inj₂ notinl' =
  ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αA) (whrDet* (red D₁ , ne neK)
                 (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 [A']) [B'] f<
  | TS.inj₂ notinl' = emb⁰¹ (ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<)
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
  | TS.inj₂ notinl' 
  with whrDet* (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA) ) ((red A⇒A'') , αₙ αA')
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
  | TS.inj₂ notinl'  | PE.refl with αNeutralHProp (αNeNotIn notinl' αA) αA'
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
  | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
  | TS.inj₂ notinl'  | PE.refl | PE.refl | PE.refl =
    ϝᵣ-l A⇒A'' αA' [B'] tA fA (τTyLog [B']) (τTyLog [B'])
      (ShapeView≤ tAB tA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
      (ShapeView≤ fAB fA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Uᵣ UA) [B'] f<
  | TS.inj₂ notinl' = ⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))

ShapeView≤ {l' = l'} (ϝᵣ-r {n = n} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  with decidInLConNat l' n
ShapeView≤ {l' = l'} (ϝᵣ-r {n = n} {nε = nε} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  | TS.inj₁ (TS.inj₁ nε') =
    AntiRedShapeView (ShapeView≤ tAB [A'] (TyLog≤ (≤ₗ-add _ _ _ f< nε') [B]t) (≤ₗ-add _ _ _ f< nε'))
                     [A'] [B'] (idRed:*: (escape [A'])) (wfRed≤* f< B⇒B')  
ShapeView≤ {l' = l'} (ϝᵣ-r {n = n} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
  | TS.inj₁ (TS.inj₂ nε') =
    AntiRedShapeView (ShapeView≤ fAB [A'] (TyLog≤ (≤ₗ-add _ _ _ f< nε') [B]f) (≤ₗ-add _ _ _ f< nε'))
                     [A'] [B'] (idRed:*: (escape [A'])) (wfRed≤* f< B⇒B')
ShapeView≤ (ϝᵣ-r A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 [B']) f<
  | TS.inj₂ notinl' = emb¹⁰ (ShapeView≤ (ϝᵣ-r A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<)
ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Uᵣ UB) f<
  | TS.inj₂ notinl' = ⊥-elim (U≢αne αB (whnfRed* (red B⇒B') Uₙ))
ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ℕᵣ ℕB) f<
  | TS.inj₂ notinl' =
    ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
                    (whrDet* (red ℕB , ℕₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Emptyᵣ D) f<
  | TS.inj₂ notinl' = 
  ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
                    (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Unitᵣ D) f<
  | TS.inj₂ notinl' =
  ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
                    (whrDet* (red D , Unitₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f<
  | TS.inj₂ notinl' = 
  ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αB)
                    (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ne′ K D₁ neK K≡K) f<
  | TS.inj₂ notinl' =
    ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αB) (whrDet* (red D₁ , ne neK)
                   (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
  | TS.inj₂ notinl'
  with whrDet* (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB) ) ((red B⇒B'') , αₙ αB')
ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
  | TS.inj₂ notinl'  | PE.refl with αNeutralHProp (αNeNotIn notinl' αB) αB'
ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
  | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
  | TS.inj₂ notinl'  | PE.refl | PE.refl | PE.refl =
    ϝᵣ-r B⇒B'' αB' [A'] (τTyLog [A']) (τTyLog [A']) tB fB
      (ShapeView≤ tAB (τTyLog [A']) tB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
      (ShapeView≤ fAB (τTyLog [A']) fB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))



-- goodCasesℕ : ∀ {k k′}  ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
--              → Γ / lε ⊩⟨ k ⟩ A ≡ B / (ℕᵣ [A]) → ShapeView Γ k k′ A B (ℕᵣ [A]) [B]
-- goodCasesℕ ℕA (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
-- goodCasesℕ {k = k} {k′ = k′} D (Uᵣ ⊢Γ) ℕ≡U = ⊥-elim (ℕ≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ ℕ≡U)
-- goodCasesℕ D (Emptyᵣ D') (⊩ℕ≡ _ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Emptyₙ)
-- ... | ()
-- goodCasesℕ D (Unitᵣ D') (⊩ℕ≡ _ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Unitₙ)
-- ... | ()
-- goodCasesℕ D (ne′ K D₁ neK K≡K) (⊩ℕ≡ _ _ A⇒N) =
--   ⊥-elim (ℕ≢ne neK (whrDet* (A⇒N , ℕₙ) (red D₁ , ne neK)))
-- goodCasesℕ D (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩ℕ≡ _ _ A⇒N) =
--   ⊥-elim (ℕ≢B W (whrDet* (A⇒N , ℕₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- goodCasesℕ D (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩ℕ≡ _ _ A⇒N) = ⊥-elim (ℕ≢αne αB (whrDet* (A⇒N , ℕₙ) (red A⇒B , αₙ αB)))
-- goodCasesℕ D (ϝᵣ mε A⇒B αB [A]t [A]f) (ϝ⊩ℕ≡ mε' A⇒B' αB' tA≡B fA≡B)
--   rewrite whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)
--   rewrite αNeutralHProp (PE.subst (λ K → αNeutral _ K) (whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB') αB
--   rewrite NotInLConNatHProp _ _ mε' mε =
--     ϝᵣ-r A⇒B αB (ℕᵣ D) (ℕᵣ (τwfRed* D)) (ℕᵣ (τwfRed* D)) [A]t [A]f
--       (goodCasesℕ ((τwfRed* D)) [A]t tA≡B)
--       (goodCasesℕ ((τwfRed* D)) [A]f fA≡B)
-- goodCasesℕ [A] (Emptyᵣ D) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
--   ⊥-elim (Empty≢αne αB (whrDet* (red D , Emptyₙ) (red B⇒B' , αₙ αB)))
-- goodCasesℕ [A] (Unitᵣ D) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
--   ⊥-elim (Unit≢αne αB (whrDet* (red D , Unitₙ) (red B⇒B' , αₙ αB)))
-- goodCasesℕ [A] (ne′ K D neK K≡K) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
--   ⊥-elim (ne≢αne neK αB (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB)))
-- goodCasesℕ [A] (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--     (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
--     ⊥-elim (B≢αne BΠ αB (whrDet* (red D , Πₙ) (red B⇒B' , αₙ αB)))
-- goodCasesℕ [A] (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--     (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
--     ⊥-elim (B≢αne BΣ αB (whrDet* (red D , Σₙ) (red B⇒B' , αₙ αB)))
-- goodCasesℕ {k = k} [A] (emb 0<1 x) A≡B =
--   emb¹⁰ (goodCasesℕ {k = k} {⁰} [A] x A≡B)

-- goodCasesΣ : ∀ {k k′} [A] ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
--           → Γ / lε ⊩⟨ k ⟩ A ≡ B / Bᵣ BΣ [A] → ShapeView Γ k k′ A B (Bᵣ BΣ [A]) [B]
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
-- ... | ()
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Σₙ)
-- ... | ()
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
-- ... | ()
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
-- ... | ()
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΠ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
--   (B₌ _ _ _ _ _ _ _ _ _ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
-- ... | ()
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--   ⊥-elim (B≢ne BΣ neK (whrDet* (D′ , Σₙ) (red D₁ , ne neK)))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [A]t [A]f)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--           ⊥-elim (B≢αne BΣ αB (whrDet* (D′ , Σₙ) (red A⇒B , αₙ αB)))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ ⊢Γ)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [ ⊢U , ⊢B , U⇒B ] αB' [A]t [A]f tA≡Σ fA≡Σ) =
--     ⊥-elim (U≢αne αB' (whrDet* (id ⊢U , Uₙ) (U⇒B , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)  B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
--       ⊥-elim (ℕ≢αne αB' (whrDet* (red x , ℕₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
--     ⊥-elim (Empty≢αne αB' (whrDet* (red x , Emptyₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
--     ⊥-elim (Unit≢αne αB' (whrDet* (red x , Unitₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
--       ⊥-elim (ne≢αne neK αB' (whrDet* (red D₁ , ne neK) (red B⇒B' , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--     (Πᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
--     ⊥-elim (B≢αne BΠ αB' (whrDet* (red D₁ , Πₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ)  with decidEqNat n m
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) | TS.inj₁ e
--       rewrite e
--       rewrite NotInLConNatHProp _ _ mε nε
--       rewrite whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB) =
--     ϝᵣ-r A⇒B αB (Bᵣ _ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ [A]t) (Bᵣ BΣ [A]f) tA≡B fA≡B
--       (goodCasesΣ [A]t tA≡B tA≡Σ) (goodCasesΣ [A]f fA≡B fA≡Σ)
-- goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) | TS.inj₂ noteq =
--     ⊥-elim (noteq (αNeutralHProp αB (PE.subst (λ K → αNeutral m K) (whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB')))
-- goodCasesΣ ΣA (Bᵣ BΣ ΣB) A≡B = Bᵥ BΣ ΣA ΣB 
-- goodCasesΣ {k = k} ΣA (emb 0<1 x) A≡B =
--           emb¹⁰ (goodCasesΣ {k = k} {⁰} ΣA x A≡B)
          
-- goodCasesΠ : ∀ {k k′} [A] ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
--           → Γ / lε ⊩⟨ k ⟩ A ≡ B / Bᵣ BΠ [A] → ShapeView Γ k k′ A B (Bᵣ BΠ [A]) [B]
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
-- ... | ()
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)
-- ... | ()
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)
-- ... | ()
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Πₙ)
-- ... | ()
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
--   (B₌ _ _ _ _ _ _ _ _ _ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
-- ... | ()
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--   ⊥-elim (B≢ne BΠ neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [A]t [A]f)
--           (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--           ⊥-elim (B≢αne BΠ αB (whrDet* (D′ , Πₙ) (red A⇒B , αₙ αB)))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ ⊢Γ)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [ ⊢U , ⊢B , U⇒B ] αB' [A]t [A]f tA≡Π fA≡Π) =
--     ⊥-elim (U≢αne αB' (whrDet* (id ⊢U , Uₙ) (U⇒B , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)  B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
--       ⊥-elim (ℕ≢αne αB' (whrDet* (red x , ℕₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
--     ⊥-elim (Empty≢αne αB' (whrDet* (red x , Emptyₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
--     ⊥-elim (Unit≢αne αB' (whrDet* (red x , Unitₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
--       ⊥-elim (ne≢αne neK αB' (whrDet* (red D₁ , ne neK) (red B⇒B' , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--     (Σᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--     (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
--     ⊥-elim (B≢αne BΣ αB' (whrDet* (red D₁ , Σₙ) (red B⇒B' , αₙ αB')))
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π)  with decidEqNat n m
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) | TS.inj₁ e
--       rewrite e
--       rewrite NotInLConNatHProp _ _ mε nε
--       rewrite whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB) =
--     ϝᵣ-r A⇒B αB (Bᵣ _ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ [A]t) (Bᵣ BΠ [A]f) tA≡B fA≡B
--       (goodCasesΠ [A]t tA≡B tA≡Π) (goodCasesΠ [A]f fA≡B fA≡Π)
-- goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
--     (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) | TS.inj₂ noteq =
--     ⊥-elim (noteq (αNeutralHProp αB (PE.subst (λ K → αNeutral m K) (whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB')))
-- goodCasesΠ ΠA (Bᵣ BΠ ΠB) A≡B = Bᵥ BΠ ΠA ΠB 
-- goodCasesΠ {k = k} ΠA (emb 0<1 x) A≡B =
--           emb¹⁰ (goodCasesΠ {k = k} {⁰} ΠA x A≡B)


-- -- Construct an shape view from an equality (aptly named)
-- goodCases : ∀ {k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
--           → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A] → ShapeView Γ k k′ A B [A] [B]
-- -- Diagonal cases
-- goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
-- goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
-- goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB
-- goodCases (ne neA) (ne neB) A≡B = ne neA neB
-- goodCases (Bᵣ BΠ ΠA) (Bᵣ BΠ ΠB) A≡B = Bᵥ BΠ ΠA ΠB
-- goodCases (Bᵣ BΣ ΣA) (Bᵣ BΣ ΣB) A≡B = Bᵥ BΣ ΣA ΣB
-- goodCases (ϝᵣ {m = m} nε A⇒B αB [B]t [B]f) (ϝᵣ {m = m'} nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) with decidEqNat m m'
-- goodCases (ϝᵣ nε A⇒B αB [B]t [B]f) (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nε' =
--   ϝᵣ-l A⇒B αB (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') [B]t [B]f (AntiRedLog [B]t' (τwfRed* A⇒B')) (AntiRedLog [B]f' (τwfRed* A⇒B')) (goodCases [B]t (AntiRedLog [B]t' (τwfRed* A⇒B')) tA≡B) (goodCases [B]f (AntiRedLog [B]f' (τwfRed* A⇒B')) fA≡B)
-- goodCases (ϝᵣ {m = m} nε A⇒B αB [B]t [B]f) (ϝᵣ {m = m'} nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) | TS.inj₂ noteq =
--   let kε = λ b → NotInThereNat _ nε' _ b (DifferentDifferentNat _ _ λ e → noteq (PE.sym e)) in
--   let ϝε = λ b → (ϝᵣ (kε b) (τwfRed* {_} {_} {_} {_} {_} {_} {_} {_} {nε} A⇒B') (αNeNotIn (kε b) αB')
--                      (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [B]t')
--                      (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [B]f'))
--   in
--   ϝᵣ-l A⇒B αB (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') [B]t [B]f (ϝε Btrue) (ϝε Bfalse)
--     (goodCases [B]t (ϝε Btrue) tA≡B) (goodCases [B]f (ϝε Bfalse) fA≡B)

-- --goodCases (Σᵣ ΣA) (Σᵣ ΣB) A≡B = Σᵥ ΣA ΣB

-- goodCases {k = k} [A] (emb 0<1 x) A≡B =
--   emb¹⁰ (goodCases {k = k} {⁰} [A] x A≡B)
-- goodCases {k′ = k} (emb 0<1 x) [B] A≡B =
--   emb⁰¹ (goodCases {k = ⁰} {k} x [B] A≡B)

-- -- Refutable cases
-- -- U ≡ _
-- goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- ... | ()
-- goodCases (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- ... | ()
-- goodCases (Uᵣ′ _ _ ⊢Γ) (Unitᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- ... | ()
-- goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) PE.refl =
--   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- goodCases (Uᵣ′ _ _ ⊢Γ) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
--   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- goodCases (Uᵣ′ _ _ ⊢Γ) (ϝᵣ mε A⇒B αB [A]t [A]f) PE.refl =
--   ⊥-elim (U≢αne αB (whnfRed* (red A⇒B) Uₙ))

-- -- ℕ ≡ _
-- goodCases (ℕᵣ ℕA) [B] A≡B = goodCasesℕ ℕA [B] A≡B
      
-- -- Empty ≢ _
-- goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
-- ... | ()
-- goodCases (Emptyᵣ _) (Unitᵣ D') D with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
-- ... | ()
-- goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
-- ... | ()
-- goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
--   ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
-- goodCases (Emptyᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
--   ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- goodCases (Emptyᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B =
--  ⊥-elim (Empty≢αne αB (whrDet* (A≡B , Emptyₙ) (red A⇒B , αₙ αB)))


-- -- Unit ≡ _
-- goodCases (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
-- ... | ()
-- goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
-- ... | ()
-- goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
-- ... | ()
-- goodCases (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B =
--   ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
-- goodCases (Unitᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
--   ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- goodCases (Unitᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B =
--   ⊥-elim (Unit≢αne αB (whrDet* (A≡B , Unitₙ) (red A⇒B , αₙ αB)))

-- -- ne ≡ _
-- goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
--   ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
-- goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
--   ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
--   ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (Unitᵣ D₁) (ne₌ M D′ neM K≡M) =
--   ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
--   ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (ϝᵣ mε A⇒B αB [A]t [A]f)  (ne₌ M D′ neM K≡M) =
--   ⊥-elim (ne≢αne neM αB (whrDet* (red D′ , ne neM) (red A⇒B , αₙ αB)))


-- -- Π ≡ _
-- goodCases (Bᵣ BΠ ΠA) ⊢B A≡B = goodCasesΠ ΠA ⊢B A≡B
    

-- -- Σ ≡ _
-- goodCases (Bᵣ BΣ ΣA) ⊢B A≡B = goodCasesΣ ΣA ⊢B A≡B

-- -- ϝ ≡ _
-- goodCases (ϝᵣ mε A⇒B αB [A]t [A]f) (Uᵣ (Uᵣ j' j< ⊢Γ)) ( tA≡U , fA≡U ) = ϝᵣ-l A⇒B αB (Uᵣ (Uᵣ j' j< ⊢Γ)) [A]t [A]f (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) (goodCases [A]t (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) tA≡U) (goodCases [A]f (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) fA≡U)
-- goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (ℕᵣ D) (tA≡ℕ , fA≡ℕ) =
--   ϝᵣ-l A⇒B αB (ℕᵣ D) [B]t [B]f (ℕᵣ (τwfRed* D)) (ℕᵣ (τwfRed* D))
--     (goodCases [B]t (ℕᵣ (τwfRed* D)) tA≡ℕ)
--     (goodCases [B]f (ℕᵣ (τwfRed* D)) fA≡ℕ)
-- goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Emptyᵣ D) (tA≡B , fA≡B) =
--   ϝᵣ-l A⇒B αB (Emptyᵣ D) [B]t [B]f (Emptyᵣ (τwfRed* D)) (Emptyᵣ (τwfRed* D))
--     (goodCases [B]t (Emptyᵣ (τwfRed* D)) tA≡B)
--     (goodCases [B]f (Emptyᵣ (τwfRed* D)) fA≡B)
-- goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Unitᵣ D) (tA≡B , fA≡B) =
--   ϝᵣ-l A⇒B αB (Unitᵣ D) [B]t [B]f (Unitᵣ (τwfRed* D)) (Unitᵣ (τwfRed* D))
--     (goodCases [B]t (Unitᵣ (τwfRed* D)) tA≡B)
--     (goodCases [B]f (Unitᵣ (τwfRed* D)) fA≡B)
-- goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (ne′ K D₁ neK K≡K) (tA≡B , fA≡B) =
--   ϝᵣ-l A⇒B αB (ne′ K D₁ neK K≡K) [B]t [B]f (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) (ne′ K (τwfRed* D₁) neK (~-τ K≡K))
--     (goodCases [B]t (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) tA≡B)
--     (goodCases [B]f (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) fA≡B)
-- goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (tA≡B , fA≡B) =
--   ϝᵣ-l A⇒B αB (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) [B]t [B]f
--     (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
--          (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext)
--     (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
--          (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext)
--     (goodCases [B]t (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
--          (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext) tA≡B)
--     (goodCases [B]f (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
--          (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext) fA≡B)

-- -- Construct an shape view between two derivations of the same type
-- goodCasesRefl : ∀ {k k′ A} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([A′] : Γ / lε ⊩⟨ k′ ⟩ A)
--               → ShapeView Γ k k′ A A [A] [A′]
-- goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])





-- (ℕᵣ ℕB) A⇒A'' B⇒B'' = ?
-- (Emptyᵣ D) A⇒A'' B⇒B'' = ?
-- (Unitᵣ D) A⇒A'' B⇒B'' = ?
-- (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = ? 
-- (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' = ?
-- (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = ?



-- -- A view for constructor equality between three types
-- data ShapeView₃ (Γ : Con Term n) : ∀ {l : LCon} {lε : ⊢ₗ l} k k′ k″ A B C
--                  (p : Γ / lε ⊩⟨ k   ⟩ A)
--                  (q : Γ / lε ⊩⟨ k′  ⟩ B)
--                  (r : Γ / lε ⊩⟨ k″ ⟩ C) → Set where
--   Uᵥ : ∀ {l lε k k′ k″} UA UB UC → ShapeView₃ Γ {l} {lε} k k′ k″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
--   ℕᵥ : ∀ {A B C k k′ k″} ℕA ℕB ℕC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
--   Emptyᵥ : ∀ {l} {lε}  {A B C k k′ k″} EmptyA EmptyB EmptyC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
--   Unitᵥ : ∀ {l} {lε}  {A B C k k′ k″} UnitA UnitB UnitC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
--   ne  : ∀ {l} {lε}  {A B C k k′ k″} neA neB neC
--       → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ne neA) (ne neB) (ne neC)
--   Bᵥ : ∀ {l} {lε}  {A B C k k′ k″} W BA BB BC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W BC)
--   ϝᵣ-l : ∀ {l lε n nε} {k k' k'' A A' B C} A⇒A' αA [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A' B C [A]t [B]t [C]t
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A' B C [A]f [B]f [C]f
--          → ShapeView₃ Γ {l} {lε}                  k k' k'' A  B C (ϝᵣ nε A⇒A' αA [A]t [A]f) [B] [C]
--   ϝᵣ-m : ∀ {l lε n nε} {k k' k'' A B B' C} B⇒B' αB [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B' C [A]t [B]t [C]t
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B' C [A]f [B]f [C]f
--          → ShapeView₃ Γ {l} {lε}                  k k' k'' A B  C [A] (ϝᵣ nε B⇒B' αB [B]t [B]f) [C]
--   ϝᵣ-r : ∀ {l lε n nε} {k k' k'' A B C C'} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C' [A]t [B]t [C]t
--          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C' [A]f [B]f [C]f
--          → ShapeView₃ Γ {l} {lε}                  k k' k'' A B C  [A]  [B] (ϝᵣ nε C⇒C' αC [C]t [C]f)
--   emb⁰¹¹ : ∀ {l} {lε}  {A B C k k′ p q r}
--          → ShapeView₃ Γ {l} {lε}  ⁰ k k′ A B C p q r
--          → ShapeView₃ Γ {l} {lε}  ¹ k k′ A B C (emb 0<1 p) q r
--   emb¹⁰¹ : ∀ {l} {lε}  {A B C k k′ p q r}
--          → ShapeView₃ Γ {l} {lε}  k ⁰ k′ A B C p q r
--          → ShapeView₃ Γ {l} {lε}  k ¹ k′ A B C p (emb 0<1 q) r
--   emb¹¹⁰ : ∀ {l} {lε}  {A B C k k′ p q r}
--          → ShapeView₃ Γ {l} {lε}  k k′ ⁰ A B C p q r
--          → ShapeView₃ Γ {l} {lε}  k k′ ¹ A B C p q (emb 0<1 r)



-- -- AntiRedShapeView₃ (Uᵥ (Uᵣ j j< ⊢Γ) (Uᵣ j' j<' ⊢Γ') (Uᵣ j'' j<'' ⊢Γ'')) A⇒A' B⇒B' C⇒C'
-- --   with redU* (red A⇒A') with redU* (red B⇒B') with redU* (red C⇒C')
-- -- AntiRedShapeView₃ (Uᵥ (Uᵣ j j< ⊢Γ) (Uᵣ j' j<' ⊢Γ') (Uᵣ j'' j<'' ⊢Γ'')) A⇒A' B⇒B' C⇒C' | PE.refl | PE.refl | PE.refl =
-- --   _ , (_ , (_ ,  (Uᵥ (Uᵣ j j< ⊢Γ) (Uᵣ j' j<' ⊢Γ') (Uᵣ j'' j<'' ⊢Γ''))))
-- -- AntiRedShapeView₃ (Emptyᵥ EmptyA EmptyB EmptyC) A⇒A' B⇒B' C⇒C' =
-- --   _ , (_ , (_ , Emptyᵥ (:⇒:*-comp A⇒A' EmptyA) (:⇒:*-comp B⇒B' EmptyB) (:⇒:*-comp C⇒C' EmptyC)))
-- -- AntiRedShapeView₃ (Unitᵥ UnitA UnitB UnitC) A⇒A' B⇒B' C⇒C' =
-- --   _ , (_ , (_ , Unitᵥ (:⇒:*-comp A⇒A' UnitA) (:⇒:*-comp B⇒B' UnitB) (:⇒:*-comp C⇒C' UnitC)))
-- -- AntiRedShapeView₃ (ℕᵥ ℕA ℕB ℕC) A⇒A' B⇒B' C⇒C' = _ , (_ , (_ , ℕᵥ (:⇒:*-comp A⇒A' ℕA) (:⇒:*-comp B⇒B' ℕB) (:⇒:*-comp C⇒C' ℕC)))
-- -- AntiRedShapeView₃ (ne (ne A D neA A≡A) (ne B D' neB B≡B) (ne C D'' neC C≡C)) A⇒A' B⇒B' C⇒C' =
-- --   _ , (_ , (_ , ne (ne A (:⇒:*-comp A⇒A' D) neA A≡A) (ne B (:⇒:*-comp B⇒B' D') neB B≡B) (ne C (:⇒:*-comp C⇒C' D'') neC C≡C)))
-- -- AntiRedShapeView₃ (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- --                         (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext')
-- --                         (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F]'' [G]'' G-ext'')) A⇒A' B⇒B' C⇒C' =
-- --      _ , (_ , (_ , Bᵥ W (Bᵣ F G (:⇒:*-comp A⇒A' D) ⊢F ⊢G A≡A (λ {_} {l'} {≤ε} → [F] {_} {l'} {≤ε}) [G] G-ext)
-- --                         (Bᵣ F' G' (:⇒:*-comp B⇒B' D') ⊢F' ⊢G' A≡A' (λ {_} {l'} {≤ε} → [F]' {_} {l'} {≤ε}) [G]' G-ext')
-- --                         (Bᵣ F'' G'' (:⇒:*-comp C⇒C' D'') ⊢F'' ⊢G'' A≡A'' (λ {_} {l'} {≤ε} → [F]'' {_} {l'} {≤ε}) [G]'' G-ext'')))
-- -- AntiRedShapeView₃ (emb⁰¹¹ A) A⇒A' B⇒B' C⇒C' =
-- --   let (p' , (q' , (r' , pqr' ))) = (AntiRedShapeView₃ A A⇒A' B⇒B' C⇒C')
-- --   in
-- --   _ , (_ , (_ , emb⁰¹¹ pqr' ))
-- -- AntiRedShapeView₃ (emb¹⁰¹ A)  A⇒A' B⇒B' C⇒C' =
-- --   let (p' , (q' , (r' , pqr' ))) = (AntiRedShapeView₃ A A⇒A' B⇒B' C⇒C')
-- --   in
-- --   _ , (_ , (_ , emb¹⁰¹ pqr'))
-- -- AntiRedShapeView₃ (emb¹¹⁰ A) A⇒A' B⇒B' C⇒C' =
-- --   let (p' , (q' , (r' , pqr' ))) = (AntiRedShapeView₃ A A⇒A' B⇒B' C⇒C')
-- --   in
-- --   _ , (_ , (_ , emb¹¹⁰ pqr'))
-- -- AntiRedShapeView₃ (ϝᵣ-r {n = n} C⇒C' αC' [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A⇒A' B⇒B' C⇒C'' =
-- --   let (pt , (qt , (rt , pqrt ))) = AntiRedShapeView₃ tABC (τwfRed* A⇒A') (τwfRed* B⇒B') (idRed:*: (escape [C]t))
-- --   in
-- --   let (pf , (qf , (rf , pqrf ))) = AntiRedShapeView₃ fABC (τwfRed* A⇒A') (τwfRed* B⇒B') (idRed:*: (escape [C]f))
-- --   in
-- --   ( _ , ( _ , ( _ , ϝᵣ-r (:⇒:*-comp C⇒C'' C⇒C') αC' (AntiRedLog [A] A⇒A') (AntiRedLog [B] B⇒B') pt pf qt qf rt rf pqrt pqrf )))
-- -- AntiRedShapeView₃ (ϝᵣ-m B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A⇒A' B⇒B'' C⇒C' =
-- --   let (pt , (qt , (rt , pqrt ))) = AntiRedShapeView₃ tABC (τwfRed* A⇒A') (idRed:*: (escape [B]t)) (τwfRed* C⇒C')
-- --   in
-- --   let (pf , (qf , (rf , pqrf ))) = AntiRedShapeView₃ fABC (τwfRed* A⇒A') (idRed:*: (escape [B]f)) (τwfRed* C⇒C')
-- --   in
-- --   _ , (_ , (_ , ϝᵣ-m (:⇒:*-comp B⇒B'' B⇒B') αB' (AntiRedLog [A] A⇒A') (AntiRedLog [C] C⇒C') pt pf qt qf rt rf pqrt pqrf))
-- -- AntiRedShapeView₃ (ϝᵣ-l A⇒A' αA' [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A⇒A'' B⇒B' C⇒C' =
-- --   let (pt , (qt , (rt , pqrt ))) = AntiRedShapeView₃ tABC (idRed:*: (escape [A]t)) (τwfRed* B⇒B') (τwfRed* C⇒C')
-- --   in
-- --   let (pf , (qf , (rf , pqrf ))) = AntiRedShapeView₃ fABC (idRed:*: (escape [A]f)) (τwfRed* B⇒B') (τwfRed* C⇒C')
-- --   in
-- --   _ , (_ , (_ , ϝᵣ-l (:⇒:*-comp A⇒A'' A⇒A') αA' (AntiRedLog [B] B⇒B') (AntiRedLog [C] C⇒C') pt pf qt qf rt rf pqrt pqrf ))

-- ShapeView₃≤ : ∀ {k k′ k″ j j′ j″ A B C} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
--                       {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B} {[C] : Γ / lε ⊩⟨ k″ ⟩ C}
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j′ ⟩ B) ([C]' : Γ / lε' ⊩⟨ j″ ⟩ C)
--                       → ShapeView₃ Γ k k′ k″ A B C [A] [B] [C]
--                       → ShapeView₃ Γ j j′ j″ A B C [A]' [B]' [C]'
-- ShapeView₃≤ f< [A]' [B]' [C]' Shp = {!!}


-- -- ShapeView₃≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} (lε' : ⊢ₗ l') (≤ε : l ≤ₗ l') {k k′ k″ A B C}
-- --                  {p : Γ / lε ⊩⟨ k   ⟩ A}
-- --                  {q : Γ / lε ⊩⟨ k′  ⟩ B}
-- --                  {r : Γ / lε ⊩⟨ k″ ⟩ C}
-- --                  → ShapeView₃ Γ k k′ k″ A B C p q r
-- --                  → ∃ λ p' → ∃ λ q' → ∃ λ r' → ShapeView₃ Γ {l'} {lε'} k k′ k″ A B C p' q' r'
-- -- ShapeView₃≤ _ f< (Uᵥ (Uᵣ j j< ⊢Γ) (Uᵣ j' j<' ⊢Γ') (Uᵣ j'' j<'' ⊢Γ'')) = ( _ , ( _ , ( _ , Uᵥ (Uᵣ j j< (Con≤ f< ⊢Γ)) (Uᵣ j' j<' (Con≤ f< ⊢Γ')) (Uᵣ j'' j<'' (Con≤ f< ⊢Γ'')))))
-- -- ShapeView₃≤ _ f< (Emptyᵥ EmptyA EmptyB EmptyC) = ( _ , ( _ , ( _ , Emptyᵥ (wfRed≤* f< EmptyA) (wfRed≤* f< EmptyB) (wfRed≤* f< EmptyC))))
-- -- ShapeView₃≤ _ f< (Unitᵥ UnitA UnitB UnitC) = ( _ , ( _ , ( _ , Unitᵥ (wfRed≤* f< UnitA) (wfRed≤* f< UnitB) (wfRed≤* f< UnitC))))
-- -- ShapeView₃≤ _ f< (ℕᵥ ℕA ℕB ℕC) = ( _ , ( _ , ( _ , ℕᵥ (wfRed≤* f< ℕA) (wfRed≤* f< ℕB) (wfRed≤* f< ℕC))))
-- -- ShapeView₃≤ _ f< (ne (ne A D neA A≡A) (ne B D' neB B≡B) (ne C D'' neC C≡C)) =
-- --   ( _ , ( _ , ( _ , ne (ne A (wfRed≤* f< D) neA (~-≤ f< A≡A)) (ne B (wfRed≤* f< D') neB (~-≤ f< B≡B)) (ne C (wfRed≤* f< D'') neC (~-≤ f< C≡C)))))
-- -- ShapeView₃≤ _ f< (Bᵥ W WA WB WC) = ( _ , ( _ , ( _ , Bᵥ W (LogRel.⊩¹B≤ _ _ _ W f< WA) (LogRel.⊩¹B≤ _ _ _ W f< WB) (LogRel.⊩¹B≤ _ _ _ W f< WC))))
-- -- ShapeView₃≤ _ f< (emb⁰¹¹ A) with (ShapeView₃≤ _ f< A)
-- -- ShapeView₃≤ _ f< (emb⁰¹¹ A) | ( p' , q' , r' , pqr' ) = emb 0<1 p' , (q' , (r' , emb⁰¹¹ pqr'))
-- -- ShapeView₃≤ _ f< (emb¹⁰¹ A)  with (ShapeView₃≤ _ f< A)
-- -- ShapeView₃≤ _ f< (emb¹⁰¹ A) | ( p' , q' , r' , pqr' ) = p' , (emb 0<1 q' , (r' , emb¹⁰¹ pqr'))
-- -- ShapeView₃≤ _ f< (emb¹¹⁰ A) with (ShapeView₃≤ _ f< A)
-- -- ShapeView₃≤ _ f< (emb¹¹⁰ A) | ( p' , q' , r' , pqr' ) = p' , (q' , (emb 0<1 r' , emb¹¹⁰ pqr'))
-- -- ShapeView₃≤ {l' = l'} _ f< (ϝᵣ-r {n = n} C⇒C' αC' [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) with decidInLConNat l' n 
-- -- ShapeView₃≤ lε' f< (ϝᵣ-r {n = n} C⇒C' αC' [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₁ inl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') tABC
-- --   in
-- --   let (pt' , (qt' , (rt' , pqrt' ))) = AntiRedShapeView₃ pqrt (idRed:*: (Ty≤ f< (escape [A]))) (idRed:*: (Ty≤ f< (escape [B]))) (wfRed≤* f< C⇒C')
-- --   in
-- --   pt' , (qt' , ( rt' , (pqrt'))) 
-- -- ShapeView₃≤ lε' f< (ϝᵣ-r {n = n} C⇒C' αC' [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₂ inl')  =
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') fABC
-- --   in
-- --   let (pf' , (qf' , (rf' , pqrf' ))) = AntiRedShapeView₃ pqrf (idRed:*: (Ty≤ f< (escape [A]))) (idRed:*: (Ty≤ f< (escape [B]))) (wfRed≤* f< C⇒C')
-- --   in
-- --   pf' , (qf' , ( rf' , (pqrf'))) 
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-r {n = n} C⇒C' αC' [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | (TS.inj₂ noinl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) tABC
-- --   in
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) fABC
-- --   in
-- --   _ , (_ , (_ , ϝᵣ-r (wfRed≤* f< C⇒C') (αNeNotIn noinl' αC') (TyLog≤ f< [A]) (TyLog≤ f< [B]) pt pf qt qf rt rf pqrt pqrf))
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-m {n = n} B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC)  with decidInLConNat l' n
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-m B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₁ inl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') tABC
-- --   in
-- --   let (pt' , (qt' , (rt' , pqrt' ))) = AntiRedShapeView₃ pqrt (idRed:*: (Ty≤ f< (escape [A]))) (wfRed≤* f< B⇒B') (idRed:*: (Ty≤ f< (escape [C])))
-- --   in
-- --   pt' , (qt' , ( rt' , (pqrt')))
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-m B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₂ inl') =
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') fABC
-- --   in
-- --   let (pf' , (qf' , (rf' , pqrf' ))) = AntiRedShapeView₃ pqrf (idRed:*: (Ty≤ f< (escape [A]))) (wfRed≤* f< B⇒B') (idRed:*: (Ty≤ f< (escape [C])))
-- --   in
-- --   pf' , (qf' , ( rf' , (pqrf'))) 
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-m B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | (TS.inj₂ noinl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) tABC
-- --   in
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) fABC
-- --   in
-- --   _ , (_ , (_ , ϝᵣ-m (wfRed≤* f< B⇒B') (αNeNotIn noinl' αB') (TyLog≤ f< [A]) (TyLog≤ f< [C]) pt pf qt qf rt rf pqrt pqrf))
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-l {n = n} A⇒A' αA' [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC)  with decidInLConNat l' n
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-l {n = n} A⇒A' αA' [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₁ inl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') tABC
-- --   in
-- --   let (pt' , (qt' , (rt' , pqrt' ))) = AntiRedShapeView₃ pqrt (wfRed≤* f< A⇒A') (idRed:*: (Ty≤ f< (escape [B]))) (idRed:*: (Ty≤ f< (escape [C])))
-- --   in
-- --   pt' , (qt' , ( rt' , (pqrt')))
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-l {n = n} A⇒A' αA' [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | TS.inj₁ (TS.inj₂ inl') =
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ lε' (≤ₗ-add _ _ _ f< inl') fABC
-- --   in
-- --   let (pf' , (qf' , (rf' , pqrf' ))) = AntiRedShapeView₃ pqrf (wfRed≤* f< A⇒A') (idRed:*: (Ty≤ f< (escape [B]))) (idRed:*: (Ty≤ f< (escape [C])))
-- --   in
-- --   pf' , (qf' , ( rf' , (pqrf'))) 
-- -- ShapeView₃≤ {l' = l'} lε' f< (ϝᵣ-l {n = n} A⇒A' αA' [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) | (TS.inj₂ noinl') =
-- --   let pt , (qt , (rt , pqrt)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) tABC
-- --   in
-- --   let pf , (qf , (rf , pqrf)) = ShapeView₃≤ (⊢ₗ• _ lε' _ _ noinl') (≤ₗ-add _ _ _ (λ _ _ nε → InThere _ (f< _ _ nε) _ _) (InHereNat _)) fABC
-- --   in
-- --   _ , (_ , (_ , ϝᵣ-l (wfRed≤* f< A⇒A') (αNeNotIn noinl' αA') (TyLog≤ f< [B]) (TyLog≤ f< [C]) pt pf qt qf rt rf pqrt pqrf))


-- LogW0 : ∀ {l : LCon} {lε : ⊢ₗ l} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
--        ([A] : Γ / lε ⊩⟨ ⁰ ⟩ A)
--        → (∃ (λ BA → [A] PE.≡ Bᵣ W BA))
-- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') = (BA' , PE.refl)
-- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') = (BA' , PE.refl)
-- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) with (whrDet* (red D , Σₙ) (red D′ , Πₙ))
-- ... | ()
-- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) with (whrDet* (red D , Πₙ) (red D′ , Σₙ))
-- ... | ()
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) =
--   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) =
--   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) =
--   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) =
--   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) = ⊥-elim (B≢ne W neK (whrDet* (red D , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb () [A]) 
-- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) = ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))


-- LogW1 : ∀ {l : LCon} {lε : ⊢ₗ l} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
--        ([A] : Γ / lε ⊩⟨ ¹ ⟩ A)
--        → (∃ (λ BA → [A] PE.≡ Bᵣ W BA)) TS.⊎ (∃ (λ BA → [A] PE.≡ emb 0<1 (Bᵣ W BA)))
-- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') = TS.inj₁ (BA' , PE.refl)
-- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') = TS.inj₁ (BA' , PE.refl)
-- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) with (whrDet* (red D , Σₙ) (red D′ , Πₙ))
-- ... | ()
-- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) with (whrDet* (red D , Πₙ) (red D′ , Σₙ))
-- ... | ()
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) =
--   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) =
--   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) =
--   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) =
--   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) = ⊥-elim (B≢ne W neK (whrDet* (red D , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- LogW1 W BA (emb 0<1 [A]) with LogW0 W BA [A]
-- LogW1 W BA (emb 0<1 [A]) | BA' , PE.refl = TS.inj₂ (BA' , PE.refl)
-- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) = ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))

-- combineW-l : ∀ W {W'} {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C BA BB [B]′ [C]}
--   → ShapeView Γ {l} {lε} k k′ A B (Bᵣ W BA) (Bᵣ W' BB)
--   → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--   → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Bᵣ W BA) (Bᵣ W' BB) [C]
-- combineW-l BΠ (Bᵥ BΠ ΠA₁ ΠB₁) (Bᵥ BΠ ΠA ΠB) = Bᵥ BΠ ΠA₁ ΠB₁ ΠB
-- combineW-l BΣ (Bᵥ BΣ ΣA₁ ΣB₁) (Bᵥ BΣ ΣA ΣB) = Bᵥ BΣ ΣA₁ ΣB₁ ΣB
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
-- combineW-l W (Bᵥ W BA BB) (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) =
--   ϝᵣ-r B⇒B' αB (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA)) (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA))
--     (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB))
--     (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) [B]t [B]f
--       (combineW-l W (Bᵥ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) tAB)
--       (combineW-l W (Bᵥ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) fAB)
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
--   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
--   ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
--   ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- combineW-l W (Bᵥ W BA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
-- combineW-l W (Bᵥ BΠ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
--   with whrDet* (red D , Πₙ) (red D′ , Σₙ)
-- ... | ()
-- combineW-l W (Bᵥ BΣ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
--   with whrDet* (red D , Σₙ) (red D′ , Πₙ)
-- ... | ()
--         --  combineW-l W (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combineW-l W [AB] [BC])
-- combineW-l W [AB] (emb⁰¹ [BC]) = (combineW-l W [AB] [BC])
-- combineW-l W [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineW-l W [AB] [BC])

-- combineU : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ UA UB C [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ U U (Uᵣ UA) (Uᵣ UB)
--           → ShapeView Γ {l} {lε} k″ k‴ U C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ U U C (Uᵣ UA) (Uᵣ UB) [C]
-- combineU (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
-- combineU [AB] (emb⁰¹ [BC]) = combineU [AB] [BC]
-- combineU [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineU [AB] [BC])
-- combineU (Uᵥ UA UB) (ℕᵥ ℕA ℕB) with whnfRed* (red ℕA) Uₙ
-- ... | ()
-- combineU (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
-- ... | ()
-- combineU (Uᵥ UA UB) (Unitᵥ UnA UnB) with whnfRed* (red UnA) Uₙ
-- ... | ()
-- combineU (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- combineU (Uᵥ UA UB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- combineU (Uᵥ UA UB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
-- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC)
--   with TyLogU [B]t
-- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) | (tUC , PE.refl)
--   with TyLogU [B]f
-- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] (Uᵣ tUC) [B]f [C]t [C]f tBC fBC)
--   | ((Uᵣ _ 0<1 ⊢Γ'') , PE.refl) | ((Uᵣ _ 0<1 ⊢Γ''') , PE.refl) =
--     ϝᵣ-r C⇒C' αC (Uᵣ (Uᵣ _ 0<1 ⊢Γ)) (Uᵣ (Uᵣ _ 0<1 ⊢Γ'))
--       (Uᵣ (Uᵣ _ 0<1 ⊢Γ'')) (Uᵣ (Uᵣ _ 0<1 ⊢Γ'''))
--       (Uᵣ (Uᵣ _ 0<1 ⊢Γ'')) (Uᵣ (Uᵣ _ 0<1 ⊢Γ''')) [C]t [C]f
--       (combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ'') (Uᵣ _ 0<1 ⊢Γ'')) tBC)
--       (combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ''') (Uᵣ _ 0<1 ⊢Γ''')) fBC)

-- combineℕ : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C ℕA ℕB [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) [C]
-- combineℕ (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
-- combineℕ [AB] (emb⁰¹ [BC]) = combineℕ [AB] [BC]
-- combineℕ [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineℕ [AB] [BC])
-- combineℕ (ℕᵥ ℕA ℕB) (Uᵥ UA UB) with whnfRed* (red ℕB) Uₙ
-- ... | ()
-- combineℕ (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
-- ... | ()
-- combineℕ (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
-- ... | ()
-- combineℕ (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
-- combineℕ (ℕᵥ ℕA ℕB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- combineℕ (ℕᵥ ℕA ℕB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (ℕ≢αne αA (whrDet* (red ℕB , ℕₙ) (red A⇒A' , αₙ αA)))
-- combineℕ (ℕᵥ ℕA ℕB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
--   ϝᵣ-r C⇒C' αC (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ (τwfRed* ℕA)) (ℕᵣ (τwfRed* ℕA))
--     (ℕᵣ (τwfRed* ℕB)) (ℕᵣ (τwfRed* ℕB)) [C]t [C]f
--     (combineℕ (ℕᵥ (τwfRed* ℕA) (τwfRed* ℕB)) tBC)
--     (combineℕ (ℕᵥ (τwfRed* ℕA) (τwfRed* ℕB)) fBC)

-- combineUnit : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C UnitA UnitB [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) [C]
-- combineUnit (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
-- combineUnit [AB] (emb⁰¹ [BC]) = combineUnit [AB] [BC]
-- combineUnit [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineUnit [AB] [BC])
-- combineUnit (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
-- ... | ()
-- combineUnit (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
-- ... | ()
-- combineUnit (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
-- ... | ()
-- combineUnit (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
-- combineUnit (Unitᵥ UnitA UnitB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (Unit≢αne αA (whrDet* (red UnitB , Unitₙ) (red A⇒A' , αₙ αA)))
-- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
--   ϝᵣ-r C⇒C' αC (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ (τwfRed* UnitA)) (Unitᵣ (τwfRed* UnitA))
--     (Unitᵣ (τwfRed* UnitB)) (Unitᵣ (τwfRed* UnitB)) [C]t [C]f
--     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) tBC)
--     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) fBC)


-- combineE : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C EA EB [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EA) (Emptyᵣ EB)
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Emptyᵣ EA) (Emptyᵣ EB) [C]
-- combineE (Emptyᵥ EA₁ EB₁) (Emptyᵥ EA EB) = Emptyᵥ EA₁ EB₁ EB
-- combineE [AB] (emb⁰¹ [BC]) = combineE [AB] [BC]
-- combineE [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineE [AB] [BC])
-- combineE (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
-- ... | ()
-- combineE (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
-- ... | ()
-- combineE (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
-- ... | ()
-- combineE (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
-- combineE (Emptyᵥ EmptyA EmptyB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- combineE (Emptyᵥ EmptyA EmptyB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (Empty≢αne αA (whrDet* (red EmptyB , Emptyₙ) (red A⇒A' , αₙ αA)))
-- combineE (Emptyᵥ EA EB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
--   ϝᵣ-r C⇒C' αC (Emptyᵣ EA) (Emptyᵣ EB) (Emptyᵣ (τwfRed* EA)) (Emptyᵣ (τwfRed* EA))
--     (Emptyᵣ (τwfRed* EB)) (Emptyᵣ (τwfRed* EB)) [C]t [C]f
--     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) tBC)
--     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) fBC)


-- combineNe : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C neA neB [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB)
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (ne neA) (ne neB) [C]
-- combineNe (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
-- combineNe [AB] (emb⁰¹ [BC]) = combineNe [AB] [BC]
-- combineNe [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineNe [AB] [BC])
-- combineNe (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
--   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- combineNe (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
--   ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
-- combineNe (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
--   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
-- combineNe (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
--   ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
-- combineNe (ne neA (ne K D neK K≡K)) (Bᵥ W (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
-- combineNe (ne neA (ne K D neK K≡K)) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
-- combineNe (ne (ne K D neK K≡K) (ne K' D' neK' K≡K')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) = 
--   ϝᵣ-r C⇒C' αC (ne (ne K D neK K≡K)) (ne (ne K' D' neK' K≡K'))
--     (ne (ne K (τwfRed* D) neK (~-τ K≡K))) (ne (ne K (τwfRed* D) neK (~-τ K≡K)))
--     (ne (ne K' (τwfRed* D') neK' (~-τ K≡K'))) (ne (ne K' (τwfRed* D') neK' (~-τ K≡K'))) [C]t [C]f
--     (combineNe (ne (ne K (τwfRed* D) neK (~-τ K≡K)) (ne K' (τwfRed* D') neK' (~-τ K≡K'))) tBC)
--     (combineNe (ne (ne K (τwfRed* D) neK (~-τ K≡K)) (ne K' (τwfRed* D') neK' (~-τ K≡K'))) fBC)



-- -- ϝᵣ-r C⇒C' αC (Uᵣ (Uᵣ j j< ⊢Γ)) (Uᵣ (Uᵣ j' j<' ⊢Γ')) (Uᵣ (Uᵣ j j< (τCon _ _ _ _ ⊢Γ))) (Uᵣ (Uᵣ j j< (τCon _ _ _ _ ⊢Γ))) (Uᵣ (Uᵣ j' j<' (τCon _ _ _ _ ⊢Γ))) (Uᵣ (Uᵣ j' j<' (τCon _ _ _ _ ⊢Γ))) [C]t [C]f (combine (Uᵥ (Uᵣ j j< (τCon _ _ _ _ ⊢Γ)) (Uᵣ j' j<' (τCon _ _ _ _ ⊢Γ))) tBC) {!!}


-- mutual

--   AntiRedShapeView₃' :  ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ j j′ j″ A A' B B' C C'}
--                  {p' : Γ / lε ⊩⟨ k   ⟩ A'}
--                  {q' : Γ / lε ⊩⟨ k′  ⟩ B'}
--                  {r' : Γ / lε ⊩⟨ k″ ⟩ C'}
--                  (pqr' : ShapeView₃  Γ k k′ k″ A' B' C' p' q' r')
--                  (A⇒A' : Γ / lε ⊢ A :⇒*: A')
--                  (B⇒B' : Γ / lε ⊢ B :⇒*: B')
--                  (C⇒C' : Γ / lε ⊢ C :⇒*: C')
--                  (p : Γ / lε ⊩⟨ j   ⟩ A)
--                  (q : Γ / lε ⊩⟨ j′  ⟩ B)
--                  (r : Γ / lε ⊩⟨ j″ ⟩ C)
--                  → ShapeView₃ Γ {l} {lε} j j′ j″ A B C p q r
--   AntiRedShapeView₃' pqr' A⇒A' B⇒B' C⇒C' p q r = {!!}

--   RedShapeView₃ :  ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ j j′ j″ A A' B B' C C'}
--                  {p : Γ / lε ⊩⟨ k   ⟩ A}
--                  {q : Γ / lε ⊩⟨ k′  ⟩ B}
--                  {r : Γ / lε ⊩⟨ k″ ⟩ C}
--                  (pqr : ShapeView₃  Γ k k′ k″ A B C p q r)
--                  (A⇒A' : Γ / lε ⊢ A :⇒*: A')
--                  (B⇒B' : Γ / lε ⊢ B :⇒*: B')
--                  (C⇒C' : Γ / lε ⊢ C :⇒*: C')
--                  (p' : Γ / lε ⊩⟨ j   ⟩ A')
--                  (q' : Γ / lε ⊩⟨ j′  ⟩ B')
--                  (r' : Γ / lε ⊩⟨ j″ ⟩ C')
--                  → ShapeView₃ Γ {l} {lε} j j′ j″ A' B' C' p' q' r'
--   RedShapeView₃ pqr A⇒A' B⇒B' C⇒C' p' q' r' = {!!}

  
-- --   combineW-l W (ϝᵣ-r {n = n} {nε = nε} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l {n = n'} {nε = nε'} B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --     with (whrDet* ( red B⇒B'' , αₙ αB'' ) ( red B⇒B' , αₙ αB' )) 
-- --   combineW-l W (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l {n = n'} {nε = nε'} B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl
-- --     with αNeutralHProp αB' αB''
-- --   combineW-l W (ϝᵣ-r {nε = nε} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l {nε = nε'} B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl
-- --     with NotInLConNatHProp _ _ nε nε'
-- --   combineW-l W (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB)
-- --                (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl | PE.refl =
-- --     ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] [A]t [A]f [B]t [B]f [C]t [C]f (combine tAB tBC) (combine fAB fBC)
  
-- --   --   with LogW0 W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) [A]t
-- --   -- combineW-l W {_} {_} {⁰} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ [A]f [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl | PE.refl | BAt , PE.refl 
-- --   --   with LogW0 W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) [A]f 
-- --   -- combineW-l W {_} {_} {⁰} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ _ [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | BAt , PE.refl | BAf , PE.refl =
-- --   --   ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] (Bᵣ W BAt) (Bᵣ W BAf) [B]t [B]f [C]t [C]f (combineW-l W tAB tBC) (combineW-l W fAB fBC)
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl | PE.refl
-- --   --   with LogW1 W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) [A]t 
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ [A]f [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₁ (BAt , PE.refl)
-- --   --   with LogW1 W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) [A]f 
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ _ [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₁ (BAt , PE.refl) | TS.inj₁ (BAf , PE.refl) =
-- --   --   ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] (Bᵣ W BAt) (Bᵣ W BAf) [B]t [B]f [C]t [C]f (combineW-l W tAB tBC) (combineW-l W fAB fBC)
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ _ [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₁ (BAt , PE.refl) | TS.inj₂ (BAf , PE.refl) =
-- --   --   ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] {!!} {!!} [B]t [B]f [C]t [C]f {!!} {!!}
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ [A]f [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₂ (BAt , PE.refl)
-- --   --   with LogW1 W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) [A]f 
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ _ [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₂ (BAt , PE.refl) | TS.inj₁ (BAf , PE.refl) =
-- --   --   ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] {!!} (Bᵣ W BAf) [B]t [B]f [C]t [C]f {!!} {!!}
-- --   -- combineW-l W {_} {_} {¹} (ϝᵣ-r  B⇒B' αB' (Bᵣ W BA) _ _ [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   --   | PE.refl | PE.refl | PE.refl | TS.inj₂ (BAt , PE.refl) | TS.inj₂ (BAf , PE.refl) = 
-- --   --   ϝᵣ-m B⇒B' αB' {!!} [C] {!!} {!!} [B]t [B]f [C]t [C]f {!!} {!!}
-- --   -- -- combineW-l W (ϝᵣ-r {nε = nε} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l  B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --   -- --   rewrite αNeutralHProp (PE.subst (λ K → αNeutral _ K) (whrDet* ( red B⇒B'' , αₙ αB'' ) ( red B⇒B' , αₙ αB' )) αB'') αB' =
-- --   -- --  ϝᵣ-m B⇒B' αB' (Bᵣ W BA) [C] [A]t [A]f [B]t [B]f
-- --   -- --    (PE.subst (λ mε → _ / ⊢ₗ• _ _ _ _ mε ⊩⟨ _ ⟩ _) (NotInLConNatHProp _ _ _ nε) [C]t)
-- --   -- --    (PE.subst (λ mε → _ / ⊢ₗ• _ _ _ _ mε ⊩⟨ _ ⟩ _) (NotInLConNatHProp _ _ _ nε) [C]f) {!!} {!!}
  
-- --   combineW-l W (ϝᵣ-r {n = n} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-r {n = n'} {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) with decidEqNat n n'
-- --   combineW-l W (ϝᵣ-r {nε = nε} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB)
-- --                (ϝᵣ-r {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | (TS.inj₁ PE.refl) with NotInLConNatHProp _ _ nε nε'
-- --   combineW-l W (ϝᵣ-r {n = n} {nε = nε} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB)
-- --                (ϝᵣ-r {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | (TS.inj₁ PE.refl) | PE.refl =
-- --                  ϝᵣ-m B⇒B' αB' (Bᵣ W BA) (ϝᵣ nε' C⇒C' αC' [C]t [C]f) [A]t [A]f [B]t [B]f
-- --                    (AntiRedLog [C]t (τwfRed* C⇒C')) (AntiRedLog [C]f (τwfRed* C⇒C'))
-- --                    (AntiRedShapeView₃' (combine tAB (RedShapeView tBC [B]t [C]t (τwfRed* B⇒B') (idRed:*: (escape [C]t))))
-- --                      (idRed:*: (escape [A]t)) (idRed:*: (escape [B]t)) (τwfRed* C⇒C') [A]t [B]t (AntiRedLog [C]t (τwfRed* C⇒C')))
-- --                    (AntiRedShapeView₃' (combine fAB (RedShapeView fBC [B]f [C]f (τwfRed* B⇒B') (idRed:*: (escape [C]f))))
-- --                      (idRed:*: (escape [A]f)) (idRed:*: (escape [B]f)) (τwfRed* C⇒C') [A]f [B]f (AntiRedLog [C]f (τwfRed* C⇒C')))
-- --     -- let (pt' , (qt' , (rt' , pqrt' ))) = AntiRedShapeView₃ (combine tAB (goodCases [B]t [C]t {!!})) (idRed:*: (escape [A]t)) (idRed:*: (escape [B]t)) (wfRed≤* (λ _ _ nε → InThere _ nε _ _) C⇒C')
-- --     -- in
-- --     -- ϝᵣ-m B⇒B' αB' (Bᵣ W BA) (ϝᵣ nε' C⇒C' αC' [C]t [C]f) pt' [A]f {!!} [B]f rt' {!!} (let fjzfe
-- --     --                                                                                        = (ϝᵣ-m B⇒B' αB' (Bᵣ W BA) (ϝᵣ nε' C⇒C' αC' [C]t [C]f) pt' [A]f qt'
-- --     --                                                                                            [B]f rt' {!!} {!!} {!!})
-- --     --                                                                                   in {!!}) {!!}
-- --   combineW-l W (ϝᵣ-r {n = n} B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-r {n = n'} {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | TS.inj₂ noteq =
-- --              ϝᵣ-m B⇒B' αB' (Bᵣ W BA) (ϝᵣ nε' C⇒C' αC' [C]t [C]f) [A]t [A]f [B]t [B]f
-- --              (ϝᵣ (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) (τwfRed* C⇒C')
-- --                (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))
-- --              (ϝᵣ (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) (τwfRed* C⇒C')
-- --                (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                  (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                  (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))
-- --              (combine tAB
-- --                (ϝᵣ-r (τwfRed* C⇒C') (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                  [B]t _ _ _ _
-- --                  (RedShapeView
-- --                    (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]t')
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t) tBC)
-- --                    (τTyLog [B]t)
-- --                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                    (τwfRed* (τwfRed* B⇒B'))
-- --                    (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t))))
-- --                  (RedShapeView
-- --                    (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]f')
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f) fBC)
-- --                    (τTyLog [B]t)
-- --                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f)
-- --                    (τwfRed* (τwfRed* B⇒B'))
-- --                    (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))))))
-- --              (combine fAB
-- --                (ϝᵣ-r (τwfRed* C⇒C') (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                              [B]f _ _ _ _
-- --                      (RedShapeView
-- --                        (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]t')
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t) tBC)
-- --                      (τTyLog [B]f)
-- --                      (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                      (τwfRed* (τwfRed* B⇒B'))
-- --                      (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t))))
-- --                      (RedShapeView
-- --                        (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]f')
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f) fBC)
-- --                        (τTyLog [B]f)
-- --                        (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f)
-- --                        (τwfRed* (τwfRed* B⇒B'))
-- --                        (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))))))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (Uᵥ UA UB) =
-- --     ⊥-elim (U≢αne αB' (whrDet* (id (⊢A-red B⇒B') , Uₙ) (red B⇒B' , αₙ αB')))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ℕᵥ ℕA ℕB) =
-- --     ⊥-elim (ℕ≢αne αB' (whrDet* (red ℕA , ℕₙ) (red B⇒B' , αₙ αB')))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵥ EmptyA EmptyB) =
-- --     ⊥-elim (Empty≢αne αB' (whrDet* (red EmptyA , Emptyₙ) (red B⇒B' , αₙ αB')))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (Unitᵥ UnitA UnitB) =
-- --     ⊥-elim (Unit≢αne αB' (whrDet* (red UnitA , Unitₙ) (red B⇒B' , αₙ αB')))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (ne (ne K D neK K≡K) neB) =
-- --     ⊥-elim (ne≢αne neK αB' (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB')))
-- --   combineW-l W (ϝᵣ-r B⇒B' αB' (Bᵣ W BA) [A]t [A]f [B]t [B]f tAB fAB) (Bᵥ W' (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BC) =
-- --     ⊥-elim (B≢αne W' αB' (whrDet* (red D ,  ⟦ W' ⟧ₙ) (red B⇒B' , αₙ αB')))
  
  
--   -- Combines two two-way views into a three-way view
--   combine : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C [A] [B] [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B [A] [B]
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C [A] [B] [C]
--   -- Diagonal cases
--   combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
--   combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
--   combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
--   combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])

--   -- Π/Σ ≡ _
--   combine (Bᵥ W BA BB) [BC] = combineW-l W (Bᵥ W BA BB) [BC]
  

--   -- U ≡ _
--   combine (Uᵥ UA UB) [BC] = combineU (Uᵥ UA UB) [BC]
  
--   -- ℕ ≡ _
--   combine (ℕᵥ ℕA ℕB) [BC] = combineℕ (ℕᵥ ℕA ℕB) [BC]
  
--   -- Empty ≡ _
--   combine (Emptyᵥ EmptyA EmptyB) = combineE (Emptyᵥ EmptyA EmptyB) 
  
--   -- Unit ≡ _
--   combine (Unitᵥ UnitA UnitB) = combineUnit (Unitᵥ UnitA UnitB)
  
--   -- ne ≡ _
--   combine (ne neA neB) = combineNe (ne neA neB)

--   -- combine (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne neB (ne K D neK K≡K)) = {!!}
--   combine {[C] = [C]} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [BC] =
--     ϝᵣ-l A⇒A' αA [B] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
--          (combine tAB (ShapeView≤ (λ n₁ b e → InThere _ e _ _) [B]t (τTyLog [C]) [BC]))
--          (combine fAB (ShapeView≤ (λ n₁ b e → InThere _ e _ _) [B]f (τTyLog [C]) [BC]))

--   combine {[B]′ = [B]′} {[C] = [C]} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [BC] =
--     ϝᵣ-m B⇒B' αB [A] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
--     (combine tAB (RedShapeView (ShapeView≤ (λ n₁ b e → InThere _ e _ _) (τTyLog [B]′) (τTyLog [C]) [BC])
--                                [B]t (τTyLog [C]) (τwfRed* B⇒B') (idRed:*: (escape (τTyLog [C])))))
--     (combine fAB (RedShapeView (ShapeView≤ (λ n₁ b e → InThere _ e _ _) (τTyLog [B]′) (τTyLog [C]) [BC])
--                                [B]f (τTyLog [C]) (τwfRed* B⇒B') (idRed:*: (escape (τTyLog [C])))))

-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (ne neB (ne K D neK K≡K)) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵥ UnitA UnitB) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵥ EmptyA EmptyB) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (Uᵥ UA UB) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵥ ℕA ℕB) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) = {!!}
-- -- --  combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l B⇒B'' αB' [C] [B]t' [B]f' [C]t [C]f tBC fBC) = {!!}
-- --   combine (ϝᵣ-r B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC)
-- --     with (whrDet* ( red B⇒B'' , αₙ αB'' ) ( red B⇒B' , αₙ αB' )) 
-- --   combine (ϝᵣ-r B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-l B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl
-- --     with αNeutralHProp αB' αB''
-- --   combine (ϝᵣ-r {nε = nε} B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-l {nε = nε'} B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl
-- --     with NotInLConNatHProp _ _ nε nε'
-- --   combine (ϝᵣ-r B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-l B⇒B'' αB'' [C] _ _ [C]t [C]f tBC fBC) | PE.refl | PE.refl | PE.refl =
-- --     ϝᵣ-m B⇒B' αB' [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f (combine tAB tBC) (combine fAB fBC)
-- -- --  combine (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ-r C⇒C' αC [B]' [B]t' [B]f' [C]t [C]f tBC fBC) = {!!}
-- --   combine (ϝᵣ-r {n = n} B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-r {n = n'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) with decidEqNat n n'
-- --   combine (ϝᵣ-r {nε = nε} B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-r {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | (TS.inj₁ PE.refl)
-- --           with NotInLConNatHProp _ _ nε nε'
-- --   combine (ϝᵣ-r {n = n} {nε = nε} B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-r C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | (TS.inj₁ PE.refl) | PE.refl =
-- --             ϝᵣ-m B⇒B' αB' [A] (ϝᵣ nε C⇒C' αC' [C]t [C]f) [A]t [A]f [B]t [B]f
-- --               (AntiRedLog [C]t (τwfRed* C⇒C')) (AntiRedLog [C]f (τwfRed* C⇒C'))
-- --               (AntiRedShapeView₃' (combine tAB (RedShapeView tBC [B]t [C]t (τwfRed* B⇒B') (idRed:*: (escape [C]t))))
-- --               (idRed:*: (escape [A]t)) (idRed:*: (escape [B]t)) (τwfRed* C⇒C') [A]t [B]t (AntiRedLog [C]t (τwfRed* C⇒C')))
-- --               (AntiRedShapeView₃' (combine fAB (RedShapeView fBC [B]f [C]f (τwfRed* B⇒B') (idRed:*: (escape [C]f))))
-- --               (idRed:*: (escape [A]f)) (idRed:*: (escape [B]f)) (τwfRed* C⇒C') [A]f [B]f (AntiRedLog [C]f (τwfRed* C⇒C')))
-- --   combine (ϝᵣ-r {n = n} B⇒B' αB' [A] [A]t [A]f [B]t [B]f tAB fAB)
-- --           (ϝᵣ-r {nε = nε'} C⇒C' αC' [C] [B]t' [B]f' [C]t [C]f tBC fBC) | TS.inj₂ noteq =
-- --             ϝᵣ-m B⇒B' αB' [A] (ϝᵣ nε' C⇒C' αC' [C]t [C]f) [A]t [A]f [B]t [B]f
-- --              (ϝᵣ (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) (τwfRed* C⇒C')
-- --                (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))
-- --              (ϝᵣ (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) (τwfRed* C⇒C')
-- --                (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                  (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                  (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))
-- --              (combine tAB
-- --                (ϝᵣ-r (τwfRed* C⇒C') (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                  [B]t _ _ _ _
-- --                  (RedShapeView
-- --                    (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]t')
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t) tBC)
-- --                    (τTyLog [B]t)
-- --                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                    (τwfRed* (τwfRed* B⇒B'))
-- --                    (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t))))
-- --                  (RedShapeView
-- --                    (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]f')
-- --                                (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f) fBC)
-- --                    (τTyLog [B]t)
-- --                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f)
-- --                    (τwfRed* (τwfRed* B⇒B'))
-- --                    (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))))))
-- --              (combine fAB
-- --                (ϝᵣ-r (τwfRed* C⇒C') (αNeNotIn (NotInThereNat _ nε' _ _ (DifferentDifferentNat _ _ (λ e → noteq (PE.sym e)))) αC')
-- --                              [B]f _ _ _ _
-- --                      (RedShapeView
-- --                        (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]t')
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t) tBC)
-- --                      (τTyLog [B]f)
-- --                      (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t)
-- --                      (τwfRed* (τwfRed* B⇒B'))
-- --                      (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]t))))
-- --                      (RedShapeView
-- --                        (ShapeView≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _))
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [B]f')
-- --                                    (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f) fBC)
-- --                        (τTyLog [B]f)
-- --                        (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f)
-- --                        (τwfRed* (τwfRed* B⇒B'))
-- --                        (idRed:*: (escape (TyLog≤ (≤ₗ-add _ _ _ (λ n b e → InThere _ (InThere _ e _ _) _ _) (InHereNat _)) [C]f))))))


-- --   -- -- Π/Σ ≡ _
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
-- --   --   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
-- --   --   ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
-- --   --   ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
-- --   --   ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- --   -- combine (Bᵥ W BA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
-- --   --   ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
-- --   -- combine (Bᵥ BΠ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
-- --   --   with whrDet* (red D , Πₙ) (red D′ , Σₙ)
-- --   -- ... | ()
-- --   -- combine (Bᵥ BΣ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
-- --   --   with whrDet* (red D , Σₙ) (red D′ , Πₙ)
-- --   -- ... | ()
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- --   --   ⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
-- --   -- combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) = {!!}
     
