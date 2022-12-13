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
  ϝᵣ-l : ∀ {l lε n nε} {k k' A A' B} A⇒A' αA [B] [A]t [A]f [B]t [B]f → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A' B [A]t [B]t
                                                                     → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A' B [A]f [B]f
                                                                     → ShapeView Γ {l} {lε} k k' A B (ϝᵣ nε A⇒A' αA [A]t [A]f) [B]
  ϝᵣ-r : ∀ {l lε n nε} {k k' A B B'} B⇒B' αB [A] [A]t [A]f [B]t [B]f → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A B' [A]t [B]t
                                                                     → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A B' [A]f [B]f
                                                                     → ShapeView Γ {l} {lε} k k' A B [A] (ϝᵣ nε B⇒B' αB [B]t [B]f)
--  ϝᵣ-r : ∀ {l lε n nε} {k k' A A' B} A⇒A' αA [A] [A]t [A]f [B]t [B]f → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A' B [A]t [B]t
--                                                                     → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A' B [A]f [B]f
--                                                                     → ShapeView Γ {l} {lε} k k' A B [A] (ϝᵣ A⇒A' αA [B]t [B]f)
  emb⁰¹ : ∀ {l} {lε} {A B k p q}
        → ShapeView Γ {l} {lε} ⁰ k A B p q
        → ShapeView Γ {l} {lε} ¹ k A B (emb 0<1 p) q
  emb¹⁰ : ∀ {l} {lε} {A B k p q}
        → ShapeView Γ {l} {lε} k ⁰ A B p q
        → ShapeView Γ {l} {lε} k ¹ A B p (emb 0<1 q)

goodCasesℕ : ∀ {k k′}  ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
             → Γ / lε ⊩⟨ k ⟩ A ≡ B / (ℕᵣ [A]) → ShapeView Γ k k′ A B (ℕᵣ [A]) [B]
goodCasesℕ ℕA (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCasesℕ {k = k} {k′ = k′} D (Uᵣ ⊢Γ) ℕ≡U = ⊥-elim (ℕ≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ ℕ≡U)
goodCasesℕ D (Emptyᵣ D') (⊩ℕ≡ _ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Emptyₙ)
... | ()
goodCasesℕ D (Unitᵣ D') (⊩ℕ≡ _ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Unitₙ)
... | ()
goodCasesℕ D (ne′ K D₁ neK K≡K) (⊩ℕ≡ _ _ A⇒N) =
  ⊥-elim (ℕ≢ne neK (whrDet* (A⇒N , ℕₙ) (red D₁ , ne neK)))
goodCasesℕ D (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩ℕ≡ _ _ A⇒N) =
  ⊥-elim (ℕ≢B W (whrDet* (A⇒N , ℕₙ) (red D₁ , ⟦ W ⟧ₙ)))
goodCasesℕ D (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩ℕ≡ _ _ A⇒N) = ⊥-elim (ℕ≢αne αB (whrDet* (A⇒N , ℕₙ) (red A⇒B , αₙ αB)))
goodCasesℕ D (ϝᵣ mε A⇒B αB [A]t [A]f) (ϝ⊩ℕ≡ mε' A⇒B' αB' tA≡B fA≡B)
  rewrite whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)
  rewrite αNeutralHProp (PE.subst (λ K → αNeutral _ K) (whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB') αB
  rewrite NotInLConNatHProp _ _ mε' mε =
    ϝᵣ-r A⇒B αB (ℕᵣ D) (ℕᵣ (τwfRed* D)) (ℕᵣ (τwfRed* D)) [A]t [A]f
      (goodCasesℕ ((τwfRed* D)) [A]t tA≡B)
      (goodCasesℕ ((τwfRed* D)) [A]f fA≡B)
goodCasesℕ [A] (Emptyᵣ D) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
  ⊥-elim (Empty≢αne αB (whrDet* (red D , Emptyₙ) (red B⇒B' , αₙ αB)))
goodCasesℕ [A] (Unitᵣ D) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
  ⊥-elim (Unit≢αne αB (whrDet* (red D , Unitₙ) (red B⇒B' , αₙ αB)))
goodCasesℕ [A] (ne′ K D neK K≡K) (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
  ⊥-elim (ne≢αne neK αB (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB)))
goodCasesℕ [A] (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
    ⊥-elim (B≢αne BΠ αB (whrDet* (red D , Πₙ) (red B⇒B' , αₙ αB)))
goodCasesℕ [A] (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (ϝ⊩ℕ≡ mε B⇒B' αB tA≡B fA≡B) =
    ⊥-elim (B≢αne BΣ αB (whrDet* (red D , Σₙ) (red B⇒B' , αₙ αB)))
goodCasesℕ {k = k} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCasesℕ {k = k} {⁰} [A] x A≡B)

goodCasesΣ : ∀ {k k′} [A] ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
          → Γ / lε ⊩⟨ k ⟩ A ≡ B / Bᵣ BΣ [A] → ShapeView Γ k k′ A B (Bᵣ BΣ [A]) [B]
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Σₙ)
... | ()
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
... | ()
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
... | ()
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΠ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ _ _ _ _ _ _ _ _ _ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
... | ()
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne BΣ neK (whrDet* (D′ , Σₙ) (red D₁ , ne neK)))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [A]t [A]f)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
          ⊥-elim (B≢αne BΣ αB (whrDet* (D′ , Σₙ) (red A⇒B , αₙ αB)))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ ⊢Γ)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [ ⊢U , ⊢B , U⇒B ] αB' [A]t [A]f tA≡Σ fA≡Σ) =
    ⊥-elim (U≢αne αB' (whrDet* (id ⊢U , Uₙ) (U⇒B , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)  B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
      ⊥-elim (ℕ≢αne αB' (whrDet* (red x , ℕₙ) (red B⇒B' , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
    ⊥-elim (Empty≢αne αB' (whrDet* (red x , Emptyₙ) (red B⇒B' , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
    ⊥-elim (Unit≢αne αB' (whrDet* (red x , Unitₙ) (red B⇒B' , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
      ⊥-elim (ne≢αne neK αB' (whrDet* (red D₁ , ne neK) (red B⇒B' , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (Πᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) =
    ⊥-elim (B≢αne BΠ αB' (whrDet* (red D₁ , Πₙ) (red B⇒B' , αₙ αB')))
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ)  with decidEqNat n m
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) | TS.inj₁ e
      rewrite e
      rewrite NotInLConNatHProp _ _ mε nε
      rewrite whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB) =
    ϝᵣ-r A⇒B αB (Bᵣ _ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ [A]t) (Bᵣ BΣ [A]f) tA≡B fA≡B
      (goodCasesΣ [A]t tA≡B tA≡Σ) (goodCasesΣ [A]f fA≡B fA≡Σ)
goodCasesΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Σ fA≡Σ) | TS.inj₂ noteq =
    ⊥-elim (noteq (αNeutralHProp αB (PE.subst (λ K → αNeutral m K) (whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB')))
goodCasesΣ ΣA (Bᵣ BΣ ΣB) A≡B = Bᵥ BΣ ΣA ΣB 
goodCasesΣ {k = k} ΣA (emb 0<1 x) A≡B =
          emb¹⁰ (goodCasesΣ {k = k} {⁰} ΣA x A≡B)
          
goodCasesΠ : ∀ {k k′} [A] ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
          → Γ / lε ⊩⟨ k ⟩ A ≡ B / Bᵣ BΠ [A] → ShapeView Γ k k′ A B (Bᵣ BΠ [A]) [B]
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whnfRed* D′ Uₙ
... | ()
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)
... | ()
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)
... | ()
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) with whrDet* (red D₁ , Unitₙ) (D′ , Πₙ)
... | ()
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (B₌ _ _ _ _ _ _ _ _ _ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′]) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
... | ()
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (B≢ne BΠ neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [A]t [A]f)
          (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
          ⊥-elim (B≢αne BΠ αB (whrDet* (D′ , Πₙ) (red A⇒B , αₙ αB)))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ ⊢Γ)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [ ⊢U , ⊢B , U⇒B ] αB' [A]t [A]f tA≡Π fA≡Π) =
    ⊥-elim (U≢αne αB' (whrDet* (id ⊢U , Uₙ) (U⇒B , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)  B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
      ⊥-elim (ℕ≢αne αB' (whrDet* (red x , ℕₙ) (red B⇒B' , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
    ⊥-elim (Empty≢αne αB' (whrDet* (red x , Emptyₙ) (red B⇒B' , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
    ⊥-elim (Unit≢αne αB' (whrDet* (red x , Unitₙ) (red B⇒B' , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
      ⊥-elim (ne≢αne neK αB' (whrDet* (red D₁ , ne neK) (red B⇒B' , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (Σᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
    (Bϝ .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) =
    ⊥-elim (B≢αne BΣ αB' (whrDet* (red D₁ , Σₙ) (red B⇒B' , αₙ αB')))
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π)  with decidEqNat n m
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) | TS.inj₁ e
      rewrite e
      rewrite NotInLConNatHProp _ _ mε nε
      rewrite whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB) =
    ϝᵣ-r A⇒B αB (Bᵣ _ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ [A]t) (Bᵣ BΠ [A]f) tA≡B fA≡B
      (goodCasesΠ [A]t tA≡B tA≡Π) (goodCasesΠ [A]f fA≡B fA≡Π)
goodCasesΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ {m = n} nε A⇒B αB tA≡B fA≡B)
    (Bϝ {m = m} {mε = mε} .(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) B⇒B' αB' [A]t [A]f tA≡Π fA≡Π) | TS.inj₂ noteq =
    ⊥-elim (noteq (αNeutralHProp αB (PE.subst (λ K → αNeutral m K) (whrDet* (red B⇒B' , αₙ αB') (red A⇒B , αₙ αB)) αB')))
goodCasesΠ ΠA (Bᵣ BΠ ΠB) A≡B = Bᵥ BΠ ΠA ΠB 
goodCasesΠ {k = k} ΠA (emb 0<1 x) A≡B =
          emb¹⁰ (goodCasesΠ {k = k} {⁰} ΠA x A≡B)


-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
          → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A] → ShapeView Γ k k′ A B [A] [B]
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (Bᵣ BΠ ΠA) (Bᵣ BΠ ΠB) A≡B = Bᵥ BΠ ΠA ΠB
goodCases (Bᵣ BΣ ΣA) (Bᵣ BΣ ΣB) A≡B = Bᵥ BΣ ΣA ΣB
goodCases (ϝᵣ {m = m} nε A⇒B αB [B]t [B]f) (ϝᵣ {m = m'} nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) with decidEqNat m m'
goodCases (ϝᵣ nε A⇒B αB [B]t [B]f) (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nε' =
  ϝᵣ-l A⇒B αB (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') [B]t [B]f (escapeAux [B]t' (τwfRed* A⇒B')) (escapeAux [B]f' (τwfRed* A⇒B')) (goodCases [B]t (escapeAux [B]t' (τwfRed* A⇒B')) tA≡B) (goodCases [B]f (escapeAux [B]f' (τwfRed* A⇒B')) fA≡B)
goodCases (ϝᵣ {m = m} nε A⇒B αB [B]t [B]f) (ϝᵣ {m = m'} nε' A⇒B' αB' [B]t' [B]f') ( tA≡B , fA≡B ) | TS.inj₂ noteq =
  let kε = λ b → NotInThereNat _ nε' _ b (DifferentDifferentNat _ _ λ e → noteq (PE.sym e)) in
  let ϝε = λ b → (ϝᵣ (kε b) (τwfRed* {_} {_} {_} {_} {_} {_} {_} {_} {nε} A⇒B') (αNeNotIn (kε b) αB')
                     (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [B]t')
                     (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [B]f'))
  in
  ϝᵣ-l A⇒B αB (ϝᵣ nε' A⇒B' αB' [B]t' [B]f') [B]t [B]f (ϝε Btrue) (ϝε Bfalse)
    (goodCases [B]t (ϝε Btrue) tA≡B) (goodCases [B]f (ϝε Bfalse) fA≡B)

--goodCases (Σᵣ ΣA) (Σᵣ ΣB) A≡B = Σᵥ ΣA ΣB

goodCases {k = k} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {k = k} {⁰} [A] x A≡B)
goodCases {k′ = k} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {k = ⁰} {k} x [B] A≡B)

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (Unitᵣ D) PE.refl with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) PE.refl =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (ϝᵣ mε A⇒B αB [A]t [A]f) PE.refl =
  ⊥-elim (U≢αne αB (whnfRed* (red A⇒B) Uₙ))

-- ℕ ≡ _
goodCases (ℕᵣ ℕA) [B] A≡B = goodCasesℕ ℕA [B] A≡B
      
-- Empty ≢ _
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Emptyᵣ _) (Unitᵣ D') D with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
... | ()
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D₁ , ⟦ W ⟧ₙ)))
goodCases (Emptyᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B =
 ⊥-elim (Empty≢αne αB (whrDet* (A≡B , Emptyₙ) (red A⇒B , αₙ αB)))


-- Unit ≡ _
goodCases (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
... | ()
goodCases (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
... | ()
goodCases (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
goodCases (Unitᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D₁ , ⟦ W ⟧ₙ)))
goodCases (Unitᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B =
  ⊥-elim (Unit≢αne αB (whrDet* (A≡B , Unitₙ) (red A⇒B , αₙ αB)))

-- ne ≡ _
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Unitᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (ϝᵣ mε A⇒B αB [A]t [A]f)  (ne₌ M D′ neM K≡M) =
  ⊥-elim (ne≢αne neM αB (whrDet* (red D′ , ne neM) (red A⇒B , αₙ αB)))


-- Π ≡ _
goodCases (Bᵣ BΠ ΠA) ⊢B A≡B = goodCasesΠ ΠA ⊢B A≡B
    

-- Σ ≡ _
goodCases (Bᵣ BΣ ΣA) ⊢B A≡B = goodCasesΣ ΣA ⊢B A≡B

-- ϝ ≡ _
goodCases (ϝᵣ mε A⇒B αB [A]t [A]f) (Uᵣ (Uᵣ j' j< ⊢Γ)) ( tA≡U , fA≡U ) = ϝᵣ-l A⇒B αB (Uᵣ (Uᵣ j' j< ⊢Γ)) [A]t [A]f (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) (goodCases [A]t (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) tA≡U) (goodCases [A]f (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) fA≡U)
goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (ℕᵣ D) (tA≡ℕ , fA≡ℕ) = ϝᵣ-l A⇒B αB (ℕᵣ D) [B]t [B]f (ℕᵣ (τwfRed* D)) (ℕᵣ (τwfRed* D)) (goodCases [B]t (ℕᵣ (τwfRed* D)) tA≡ℕ) (goodCases [B]f (ℕᵣ (τwfRed* D)) fA≡ℕ)
goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Emptyᵣ D) (tA≡B , fA≡B) = ϝᵣ-l A⇒B αB (Emptyᵣ D) [B]t [B]f (Emptyᵣ (τwfRed* D)) (Emptyᵣ (τwfRed* D)) (goodCases [B]t (Emptyᵣ (τwfRed* D)) tA≡B) (goodCases [B]f (Emptyᵣ (τwfRed* D)) fA≡B)
goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Unitᵣ D) (tA≡B , fA≡B) = ϝᵣ-l A⇒B αB (Unitᵣ D) [B]t [B]f (Unitᵣ (τwfRed* D)) (Unitᵣ (τwfRed* D)) (goodCases [B]t (Unitᵣ (τwfRed* D)) tA≡B) (goodCases [B]f (Unitᵣ (τwfRed* D)) fA≡B)
goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (ne′ K D₁ neK K≡K) (tA≡B , fA≡B) = ϝᵣ-l A⇒B αB (ne′ K D₁ neK K≡K) [B]t [B]f (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) (goodCases [B]t (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) tA≡B) (goodCases [B]f (ne′ K (τwfRed* D₁) neK (~-τ K≡K)) fA≡B)
goodCases (ϝᵣ mε A⇒B αB [B]t [B]f) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (tA≡B , fA≡B) =
  ϝᵣ-l A⇒B αB (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) [B]t [B]f
    (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F] (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext)
    (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F] (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext)
    (goodCases [B]t (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F] (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext) tA≡B)
    (goodCases [B]f (Bᵣ′ W F G (τwfRed* D₁) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F] (λ {m} {ρ} {Δ} {a} {l'} {f<} → [G] {m} {ρ} {Δ} {a} {l'} {≤ₗ-rev f<}) G-ext) fA≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {k k′ A} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([A′] : Γ / lε ⊩⟨ k′ ⟩ A)
              → ShapeView Γ k k′ A A [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ (Γ : Con Term n) {l : LCon} {lε : ⊢ₗ l} : ∀ k k′ k″ A B C
                 (p : Γ / lε ⊩⟨ k   ⟩ A)
                 (q : Γ / lε ⊩⟨ k′  ⟩ B)
                 (r : Γ / lε ⊩⟨ k″ ⟩ C) → Set where
  Uᵥ : ∀ {k k′ k″} UA UB UC → ShapeView₃ Γ k k′ k″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C k k′ k″} ℕA ℕB ℕC
    → ShapeView₃ Γ k k′ k″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C k k′ k″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ k k′ k″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  Unitᵥ : ∀ {A B C k k′ k″} UnitA UnitB UnitC
    → ShapeView₃ Γ k k′ k″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
  ne  : ∀ {A B C k k′ k″} neA neB neC
      → ShapeView₃ Γ k k′ k″ A B C (ne neA) (ne neB) (ne neC)
  Bᵥ : ∀ {A B C k k′ k″} W BA BB BC
    → ShapeView₃ Γ k k′ k″ A B C (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W BC)
  emb⁰¹¹ : ∀ {A B C k k′ p q r}
         → ShapeView₃ Γ ⁰ k k′ A B C p q r
         → ShapeView₃ Γ ¹ k k′ A B C (emb 0<1 p) q r
  emb¹⁰¹ : ∀ {A B C k k′ p q r}
         → ShapeView₃ Γ k ⁰ k′ A B C p q r
         → ShapeView₃ Γ k ¹ k′ A B C p (emb 0<1 q) r
  emb¹¹⁰ : ∀ {A B C k k′ p q r}
         → ShapeView₃ Γ k k′ ⁰ A B C p q r
         → ShapeView₃ Γ k k′ ¹ A B C p q (emb 0<1 r)

-- Combines two two-way views into a three-way view
combine : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C [A] [B] [B]′ [C]}
        → ShapeView Γ {l} {lε} k k′ A B [A] [B]
        → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
        → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C [A] [B] [C]
-- Diagonal cases
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (Bᵥ BΠ ΠA₁ ΠB₁) (Bᵥ BΠ ΠA ΠB) = Bᵥ BΠ ΠA₁ ΠB₁ ΠB
combine (Bᵥ BΣ ΣA₁ ΣB₁) (Bᵥ BΣ ΣA ΣB) = Bᵥ BΣ ΣA₁ ΣB₁ ΣB
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])

-- Refutable cases
-- U ≡ _
combine (Uᵥ UA UB) (ℕᵥ ℕA ℕB) with whnfRed* (red ℕA) Uₙ
... | ()
combine (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
... | ()
combine (Uᵥ UA UB) (Unitᵥ UnA UnB) with whnfRed* (red UnA) Uₙ
... | ()
combine (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (Uᵥ UA UB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))

-- ℕ ≡ _
combine (ℕᵥ ℕA ℕB) (Uᵥ UA UB) with whnfRed* (red ℕB) Uₙ
... | ()
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
... | ()
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ ℕA ℕB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))

-- Empty ≡ _
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
... | ()
combine (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine (Emptyᵥ EmptyA EmptyB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))

-- Unit ≡ _
combine (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
... | ()
combine (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
... | ()
combine (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
combine (Unitᵥ UnitA UnitB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))

-- ne ≡ _
combine (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
  ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Bᵥ W (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
  ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))

-- Π/Σ ≡ _
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
  ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
combine (Bᵥ W BA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
combine (Bᵥ BΠ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
  with whrDet* (red D , Πₙ) (red D′ , Σₙ)
... | ()
combine (Bᵥ BΣ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
  with whrDet* (red D , Σₙ) (red D′ , Πₙ)
... | ()
