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

_/_⊩⟨_⟩𝔹_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩𝔹 A = MaybeEmb k (λ k′ → Γ / lε ⊩𝔹 A)

-- _/_⊩⟨_⟩Empty_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
-- Γ / lε ⊩⟨ k ⟩Empty A = MaybeEmb k (λ k′ → Γ / lε ⊩Empty A)

-- _/_⊩⟨_⟩Unit_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
-- Γ / lε ⊩⟨ k ⟩Unit A = MaybeEmb k (λ k′ → Γ / lε ⊩Unit A)

_/_⊩⟨_⟩ne_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩ne A = MaybeEmb k (λ k′ → Γ / lε ⊩ne A)

_/_⊩⟨_⟩B⟨_⟩_ : (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (k : TypeLevel) (W : BindingType) (A : Term n) → Set
Γ / lε ⊩⟨ k ⟩B⟨ W ⟩ A = MaybeEmb k (λ k′ → Γ / lε ⊩′⟨ k′ ⟩B⟨ W ⟩ A)

-- -- Construct a general reducible type from a specific

U-intr : ∀ {k} → Γ / lε ⊩⟨ k ⟩U → Γ / lε ⊩⟨ k ⟩ U
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩ℕ A → Γ / lε ⊩⟨ k ⟩ A
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

𝔹-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩𝔹 A → Γ / lε ⊩⟨ k ⟩ A
𝔹-intr (noemb x) = 𝔹ᵣ x
𝔹-intr (emb 0<1 x) = emb 0<1 (𝔹-intr x)


-- Empty-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩Empty A → Γ / lε ⊩⟨ k ⟩ A
-- Empty-intr (noemb x) = Emptyᵣ x
-- Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

-- Unit-intr : ∀ {A k} → Γ / lε ⊩⟨ k ⟩Unit A → Γ / lε ⊩⟨ k ⟩ A
-- Unit-intr (noemb x) = Unitᵣ x
-- Unit-intr (emb 0<1 x) = emb 0<1 (Unit-intr x)

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
U-elim (𝔹ᵣ D) with whnfRed* (red D) Uₙ
... | ()
-- U-elim (Emptyᵣ D) with whnfRed* (red D) Uₙ
-- ... | ()
-- U-elim (Unitᵣ D) with whnfRed* (red D) Uₙ
-- ... | ()
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
ℕ-elim′ D (𝔹ᵣ D') with whrDet* (red D' , 𝔹ₙ) (D , ℕₙ)
... | ()
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢B W (whrDet* (D , ℕₙ) (red D′ , ⟦ W ⟧ₙ)))
-- ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
-- ... | ()
-- ℕ-elim′ D (Unitᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
-- ... | ()
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂
ℕ-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (ℕ≢αne αB (whrDet* (D , ℕₙ) (red A⇒B , αₙ αB)))

ℕ-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ ℕ → Γ / lε ⊩⟨ k ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

𝔹-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* 𝔹 → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩𝔹 A
𝔹-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , 𝔹ₙ)
... | ()
𝔹-elim′ D (ℕᵣ D') with whrDet* (D , 𝔹ₙ) (red D' , ℕₙ)
... | ()
𝔹-elim′ D (𝔹ᵣ D′) = noemb D′
𝔹-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (𝔹≢ne neK (whrDet* (D , 𝔹ₙ) (red D′ , ne neK)))
𝔹-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (𝔹≢B W (whrDet* (D , 𝔹ₙ) (red D′ , ⟦ W ⟧ₙ)))
-- ℕ-elim′ D (Emptyᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Emptyₙ)
-- ... | ()
-- ℕ-elim′ D (Unitᵣ D′) with whrDet* (D , ℕₙ) (red D′ , Unitₙ)
-- ... | ()
𝔹-elim′ D (emb 0<1 x) with 𝔹-elim′ D x
𝔹-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
𝔹-elim′ D (emb 0<1 x) | emb () x₂
𝔹-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (𝔹≢αne αB (whrDet* (D , 𝔹ₙ) (red A⇒B , αₙ αB)))

𝔹-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ 𝔹 → Γ / lε ⊩⟨ k ⟩𝔹 𝔹
𝔹-elim [𝔹] = 𝔹-elim′ (id (escape [𝔹])) [𝔹]

-- Empty-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* Empty → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩Empty A
-- Empty-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)
-- ... | ()
-- Empty-elim′ D (Emptyᵣ D′) = noemb D′
-- Empty-elim′ D (Unitᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , Unitₙ)
-- ... | ()
-- Empty-elim′ D (ne′ K D′ neK K≡K) =
--   ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
-- Empty-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
--   ⊥-elim (Empty≢B W (whrDet* (D , Emptyₙ) (red D′ , ⟦ W ⟧ₙ)))
-- Empty-elim′ D (ℕᵣ D′) with whrDet* (D , Emptyₙ) (red D′ , ℕₙ)
-- ... | ()
-- Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
-- Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
-- Empty-elim′ D (emb 0<1 x) | emb () x₂
-- Empty-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (Empty≢αne αB (whrDet* (D , Emptyₙ) (red A⇒B , αₙ αB)))

-- Empty-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ Empty → Γ / lε ⊩⟨ k ⟩Empty Empty
-- Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

-- Unit-elim′ : ∀ {A k} → Γ / lε ⊢ A ⇒* Unit → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩Unit A
-- Unit-elim′ D (Uᵣ′ k′ k< ⊢Γ) with whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Unitₙ)
-- ... | ()
-- Unit-elim′ D (Unitᵣ D′) = noemb D′
-- Unit-elim′ D (Emptyᵣ D′) with whrDet* (D , Unitₙ) (red D′ , Emptyₙ)
-- ... | ()
-- Unit-elim′ D (ne′ K D′ neK K≡K) =
--   ⊥-elim (Unit≢ne neK (whrDet* (D , Unitₙ) (red D′ , ne neK)))
-- Unit-elim′ D (Bᵣ′ W F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
--   ⊥-elim (Unit≢B W (whrDet* (D , Unitₙ) (red D′ , ⟦ W ⟧ₙ)))
-- Unit-elim′ D (ℕᵣ D′) with whrDet* (D , Unitₙ) (red D′ , ℕₙ)
-- ... | ()
-- Unit-elim′ D (emb 0<1 x) with Unit-elim′ D x
-- Unit-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
-- Unit-elim′ D (emb 0<1 x) | emb () x₂
-- Unit-elim′ D (ϝᵣ mε A⇒B αB tA fA) = ⊥-elim (Unit≢αne αB (whrDet* (D , Unitₙ) (red A⇒B , αₙ αB)))

-- Unit-elim : ∀ {k} → Γ / lε ⊩⟨ k ⟩ Unit → Γ / lε ⊩⟨ k ⟩Unit Unit
-- Unit-elim [Unit] = Unit-elim′ (id (escape [Unit])) [Unit]

ne-elim′ : ∀ {A k K} → Γ / lε ⊢ A ⇒* K → Neutral K → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊩⟨ k ⟩ne A
ne-elim′ D neK (Uᵣ′ k′ k< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (𝔹ᵣ D′) = ⊥-elim (𝔹≢ne neK (whrDet* (red D′ , 𝔹ₙ) (D , ne neK)))
-- ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
-- ne-elim′ D neK (Unitᵣ D′) = ⊥-elim (Unit≢ne neK (whrDet* (red D′ , Unitₙ) (D , ne neK)))
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
B-elim′ W D (𝔹ᵣ D′) =
   ⊥-elim (𝔹≢B W (whrDet* (red D′ , 𝔹ₙ) (D , ⟦ W ⟧ₙ)))
-- B-elim′ W D (Emptyᵣ D′) =
--   ⊥-elim (Empty≢B W (whrDet* (red D′ , Emptyₙ) (D , ⟦ W ⟧ₙ)))
-- B-elim′ W D (Unitᵣ D′) =
--   ⊥-elim (Unit≢B W (whrDet* (red D′ , Unitₙ) (D , ⟦ W ⟧ₙ)))
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
ℕ≠U [A] [B] (⊩¹≡ℕ _ A⇒N) with whnfRed* (A⇒N) Uₙ
... | ()
ℕ≠U {k = k} {k' = k'} [A] [B] (⊩¹≡ϝ-r A⇒B αB _ tA fA tA≡B fA≡B) = U≢αne αB (whrDet* (id (⊢A-red A⇒B) , Uₙ) (red A⇒B , αₙ αB))

ℕ≠𝔹 : ∀ {k} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩𝔹 B)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ B / ℕᵣ [A]) → ⊥
ℕ≠𝔹 [A] [B] (⊩¹≡ℕ _ A⇒N) with whrDet* ( red [B] , 𝔹ₙ ) ( A⇒N , ℕₙ )
... | ()
ℕ≠𝔹 {k = k} [A] [B] (⊩¹≡ϝ-r A⇒B αB _ tA fA tA≡B fA≡B) = 𝔹≢αne αB (whrDet* (red [B] , 𝔹ₙ) (red A⇒B , αₙ αB))


𝔹≠U : ∀ {k k'} ([A] : Γ / lε ⊩𝔹 A) ([B] : Γ / lε ⊩′⟨ k' ⟩U)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ U / 𝔹ᵣ [A]) → ⊥
𝔹≠U [A] [B] (⊩¹≡𝔹 _ A⇒N) with whnfRed* (A⇒N) Uₙ
... | ()
𝔹≠U {k = k} {k' = k'} [A] [B] (⊩¹≡ϝ-r A⇒B αB _ tA fA tA≡B fA≡B) = U≢αne αB (whrDet* (id (⊢A-red A⇒B) , Uₙ) (red A⇒B , αₙ αB))

𝔹≠ℕ : ∀ {k} ([A] : Γ / lε ⊩𝔹 A) ([B] : Γ / lε ⊩ℕ B)
          → (Γ / lε ⊩⟨ k ⟩ A ≡ B / 𝔹ᵣ [A]) → ⊥
𝔹≠ℕ [A] [B] (⊩¹≡𝔹 _ A⇒N) with whrDet* ( red [B] , ℕₙ ) ( A⇒N , 𝔹ₙ )
... | ()
𝔹≠ℕ {k = k} [A] [B] (⊩¹≡ϝ-r A⇒B αB _ tA fA tA≡B fA≡B) = ℕ≢αne αB (whrDet* (red [B] , ℕₙ) (red A⇒B , αₙ αB))


-- ℕ≠Unit : ∀ {k} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩Unit B)
--           → (Γ / lε ⊩⟨ k ⟩ A ≡ B / ℕᵣ [A]) → ⊥
-- ℕ≠Unit [A] [B] (⊩ℕ≡ _ _ A⇒N) with whrDet* ( red [B] , Unitₙ ) ( A⇒N , ℕₙ )
-- ... | ()
-- ℕ≠Unit {k = k} [A] [B] (ϝ⊩ℕ≡ mε A⇒B αB tA fA) = Unit≢αne αB (whrDet* (red [B] , Unitₙ) (red A⇒B , αₙ αB))

-- ℕ≠Empty : ∀ {k} ([A] : Γ / lε ⊩ℕ A) ([B] : Γ / lε ⊩Empty B)
--           → (Γ / lε ⊩⟨ k ⟩ A ≡ B / ℕᵣ [A]) → ⊥
-- ℕ≠Empty [A] [B] (⊩ℕ≡ _ _ A⇒N) with whrDet* ( red [B] , Emptyₙ ) ( A⇒N , ℕₙ )
-- ... | ()
-- ℕ≠Empty {k = k} [A] [B] (ϝ⊩ℕ≡ mε A⇒B αB tA fA) = Empty≢αne αB (whrDet* (red [B] , Emptyₙ) (red A⇒B , αₙ αB))

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {k ⊩⟨_⟩} → MaybeEmb k ⊩⟨_⟩ → ∃ λ k′ → ⊩⟨ k′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView (Γ : Con Term n) :
  ∀ {l : LCon} {lε : ⊢ₗ l} k k′ A B (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ B)
                        → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Set where
  Uᵥ : ∀ {l lε k k′} UA UB U=B → ShapeView Γ {l} {lε} k k′ U U (Uᵣ UA) (Uᵣ UB) (⊩¹≡U UA U=B)
  ℕᵥ : ∀ {l} {lε} {A B k k′} ℕA ℕB ℕ≡B → ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB) (⊩¹≡ℕ ℕA ℕ≡B)
  𝔹ᵥ : ∀ {l} {lε} {A B k k′} 𝔹A 𝔹B 𝔹≡B → ShapeView Γ {l} {lε} k k′ A B (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (⊩¹≡𝔹 𝔹A 𝔹≡B)
--  Emptyᵥ : ∀ {l} {lε} {A B k k′} EmptyA EmptyB → ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
--  Unitᵥ : ∀ {l} {lε} {A B k k′} UnitA UnitB → ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
  ne  : ∀ {l} {lε} {A B k k′} neA neB neA≡B
      → ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB) (⊩¹≡ne neA neA≡B)
  Bᵥ : ∀ {l} {lε} {A B k k′} W BA BB BA≡B
    → ShapeView Γ {l} {lε} k k′ A B (Bᵣ W BA) (Bᵣ W BB) (⊩¹≡B W BA BA≡B)
  ϝᵣ-l : ∀ {l lε n nε} {k k' A A' B} (A⇒A' : Γ / lε ⊢ A :⇒*: A') αA [B] [A]t [A]f [B]t [B]f tA≡B fA≡B
       → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A B [A]t [B]t tA≡B
       → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A B [A]f [B]f fA≡B
       → ShapeView Γ {l} {lε} k k' A B (ϝᵣ nε A⇒A' αA [A]t [A]f) [B] (⊩¹≡ϝ-l A⇒A' αA [A]t [A]f tA≡B fA≡B)
  ϝᵣ-r : ∀ {l lε n nε} {k k' A B B'} (B⇒B' B⇒B'' : Γ / lε ⊢ B :⇒*: B') αB αB' [A] [A]t [A]f [B]t [B]f tA≡B fA≡B
       → ShapeView Γ {_} {⊢ₗ• l lε n Btrue nε} k k' A B [A]t [B]t tA≡B
       → ShapeView Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' A B [A]f [B]f fA≡B
       → ShapeView Γ {l} {lε} k k' A B [A] (ϝᵣ nε B⇒B' αB [B]t [B]f) (⊩¹≡ϝ-r B⇒B'' αB' [A] [A]t [A]f tA≡B fA≡B)
  emb⁰¹ : ∀ {l} {lε} {A B k p q A≡B}
        → ShapeView Γ {l} {lε} ⁰ k A B p q A≡B
        → ShapeView Γ {l} {lε} ¹ k A B (emb 0<1 p) q (⊩¹≡emb 0<1 p A≡B)
  emb¹⁰ : ∀ {l} {lε} {A B k p q A≡B}
        → ShapeView Γ {l} {lε} k ⁰ A B p q A≡B
        → ShapeView Γ {l} {lε} k ¹ A B p (emb 0<1 q) A≡B


-- RedShapeView : ∀ {A A' B B' k k' k'' k'''} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k' ⟩ B}
--                                       ([AB] : ShapeView Γ k k' A B [A] [B])
--                                       ([A]' : Γ / lε ⊩⟨ k'' ⟩ A') ([B]' : Γ / lε ⊩⟨ k''' ⟩ B')
--                                       (A⇒A' : Γ / lε ⊢ A :⇒*: A') (B⇒B' : Γ / lε ⊢ B :⇒*: B')
--                                       → ShapeView Γ k'' k''' A' B' [A]' [B]'
-- -- The case of U
-- RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   with whnfRed* (red A⇒U) Uₙ with whnfRed* (red B⇒U) Uₙ
-- RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   | PE.refl | PE.refl with TyLogU [A]' with TyLogU [B]' 
-- RedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   | PE.refl | PE.refl | UA' , PE.refl | UB' , PE.refl = Uᵥ UA' UB'

-- -- Diagonal cases
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ℕᵣ ℕB) A⇒A'' B⇒B'' = ℕᵥ ℕA ℕB
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' = 𝔹ᵥ 𝔹A 𝔹B
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A⇒A'' B⇒B'' = Emptyᵥ EmptyA EmptyB
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Unitᵣ UnitB) A⇒A'' B⇒B'' = Unitᵥ UnitA UnitB
-- RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
--   Bᵥ BΠ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
-- RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
--   Bᵥ BΣ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
-- RedShapeView (ne neA neB) (ne neA') (ne neB') A⇒A'' B⇒B'' = ne neA' neB'
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   with whrDet* (red A⇒A' , αₙ αA) (⇒*-comp (red A⇒A′) (red A⇒A'') , αₙ αA')
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl with αNeutralHProp αA αA'
-- RedShapeView (ϝᵣ-l {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl | PE.refl | PE.refl =
--   ϝᵣ-l A⇒A'' αA' [B'] tA fA _ _
--     (RedShapeView tAB tA (τTyLog [B']) (τwfRed* A⇒A′) (τwfRed* B⇒B''))
--     (RedShapeView fAB fA (τTyLog [B']) (τwfRed* A⇒A′) (τwfRed* B⇒B''))
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   with whrDet* (red B⇒B' , αₙ αB) (⇒*-comp (red B⇒B′) (red B⇒B'') , αₙ αB')
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl with αNeutralHProp αB αB'
-- RedShapeView (ϝᵣ-r {nε = nε} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl | PE.refl | PE.refl =
--   ϝᵣ-r B⇒B'' αB' [A'] _ _ tB fB
--     (RedShapeView tAB (τTyLog [A']) tB (τwfRed* A⇒A'') (τwfRed* B⇒B′))
--     (RedShapeView fAB (τTyLog [A']) fB (τwfRed* A⇒A'') (τwfRed* B⇒B′))

-- -- Embeddings
-- RedShapeView (emb⁰¹ [AB]) = RedShapeView [AB]
-- RedShapeView (emb¹⁰ [AB]) = RedShapeView [AB]
-- RedShapeView [AB] (emb 0<1 [A]) [B] A⇒A'' B⇒B′ = emb⁰¹ (RedShapeView [AB] [A] [B] A⇒A'' B⇒B′)
-- RedShapeView [AB] [A] (emb 0<1 [B]) A⇒A'' B⇒B′ = emb¹⁰ (RedShapeView [AB] [A] [B] A⇒A'' B⇒B′)


-- -- ℕ
-- RedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whrDet* (red A⇒A'' , Uₙ) (red ℕA' , ℕₙ)
-- RedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | ()
-- RedShapeView (ℕᵥ ℕA' ℕB') (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' 
--   with whrDet* (⇒*-comp (red A⇒A'') (red 𝔹A) , 𝔹ₙ) (red ℕA' , ℕₙ)
-- ... | ()
-- -- RedShapeView (ℕᵥ ℕA' ℕB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red ℕA' , ℕₙ)
-- -- ... | ()
-- -- RedShapeView (ℕᵥ ℕA' ℕB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red ℕA' , ℕₙ)
-- -- ... | ()
-- RedShapeView (ℕᵥ ℕA' ℕB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕA' , ℕₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
-- RedShapeView (ℕᵥ ℕA' ℕB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕA') , ℕₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
-- RedShapeView (ℕᵥ ℕA' ℕB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕA' , ℕₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
--   with whrDet* (red B⇒B'' , Uₙ) (red ℕB' , ℕₙ)
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
--   | ()
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (𝔹ᵣ D) A⇒A'' B⇒B''
--   with whrDet* (⇒*-comp (red B⇒B'') (red D) , 𝔹ₙ) (red ℕB' , ℕₙ)
-- ... | ()
-- -- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Emptyᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red D) , Emptyₙ) (red ℕB' , ℕₙ)
-- -- ... | ()
-- -- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Unitᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red D) , Unitₙ) (red ℕB' , ℕₙ)
-- -- ... | ()
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕB' , ℕₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕB') , ℕₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
-- RedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕB' , ℕₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))
  
-- -- 𝔹
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whrDet* (red A⇒A'' , Uₙ) (red 𝔹A' , 𝔹ₙ)
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | ()
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' 
--   with whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red 𝔹A' , 𝔹ₙ)
-- ... | ()
-- -- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red 𝔹A' , 𝔹ₙ)
-- -- ... | ()
-- -- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red 𝔹A' , 𝔹ₙ)
-- -- ... | ()
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹A' , 𝔹ₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red 𝔹A') , 𝔹ₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red 𝔹A' , 𝔹ₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB) A⇒A'' B⇒B''
--   with whrDet* (red B⇒B'' , Uₙ) (red 𝔹B' , 𝔹ₙ)
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB) A⇒A'' B⇒B''
--   | ()
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ℕᵣ D) A⇒A'' B⇒B''
--   with whrDet* (⇒*-comp (red B⇒B'') (red D) , ℕₙ) (red 𝔹B' , 𝔹ₙ)
-- ... | ()
-- -- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Emptyᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red D) , Emptyₙ) (red 𝔹B' , 𝔹ₙ)
-- -- ... | ()
-- -- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Unitᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red D) , Unitₙ) (red 𝔹B' , 𝔹ₙ)
-- -- ... | ()
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹B' , 𝔹ₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ne′ K D neK K≡K) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red 𝔹B') , 𝔹ₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
-- RedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red 𝔹B' , 𝔹ₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))

-- -- -- Empty
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red A⇒A'' , Uₙ) (red EmptyA' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red EmptyA' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red EmptyA' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢B W (whrDet* (red EmptyA' , Emptyₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyA') , Emptyₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' = 
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyA' , Emptyₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Uᵣ UB) A⇒A'' B⇒B''
-- --   with whrDet* (red B⇒B'' , Uₙ) (red EmptyB' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ℕᵣ ℕB) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red EmptyB' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Unitᵣ UnitB) A⇒A'' B⇒B''
-- --   with whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red EmptyB' , Emptyₙ)
-- -- ... | ()
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyB' , Emptyₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyB') , Emptyₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
-- -- RedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyB' , Emptyₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- -- -- Unit
-- -- RedShapeView (Unitᵥ UnitA' UnitB')  (Uᵣ UA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red A⇒A'' , Uₙ) (red UnitA' , Unitₙ)
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) 
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) 
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' = 
-- --  ⊥-elim (Unit≢B W (whrDet* (red UnitA' , Unitₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red UnitA') , Unitₙ) (⇒*-comp (red A⇒A'') (red D) , ne neK)))
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red UnitA' , Unitₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Uᵣ UB) A⇒A'' B⇒B''
-- --   with whrDet* (red B⇒B'' , Uₙ) (red UnitB' , Unitₙ)
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ℕᵣ ℕB) A⇒A'' B⇒B''
-- --   with whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) 
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Emptyᵣ D) A⇒A'' B⇒B'' 
-- --   with whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , Emptyₙ) 
-- -- ... | ()
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* (red UnitB' , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red UnitB') , Unitₙ) (⇒*-comp (red B⇒B'') (red D) , ne neK)))
-- -- RedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red UnitB' , Unitₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- -- Σ and Π-types
-- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (U≢B W (whrDet* (red A⇒A'' , Uₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A] (Uᵣ UB) A⇒A'' B⇒B'' =
--   ⊥-elim (U≢B W (whrDet* (red B⇒B'' , Uₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' = 
--  ⊥-elim (ℕ≢B W (whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' = 
--  ⊥-elim (𝔹≢B W (whrDet* (⇒*-comp (red A⇒A'') (red 𝔹A) , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢B W (whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ne′ K' D' neK' K≡K') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK' (whrDet* ((red D) , ⟦ W ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ne neK')))
-- RedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( ⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))
-- RedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' 
--              with whrDet* (red D , ⟦ BΠ ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ BΣ ⟧ₙ)
-- RedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              | ()
-- RedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΣ ⟧ₙ) (⇒*-comp (red A⇒A'') (red D') , ⟦ BΠ ⟧ₙ)
-- RedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              | ()


-- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--  ⊥-elim (ℕ≢B W (whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--  ⊥-elim (𝔹≢B W (whrDet* (⇒*-comp (red B⇒B'') (red 𝔹B) , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
-- -- ⊥-elim (Empty≢B W (whrDet* (⇒*-comp (red B⇒B'') (red EmptyB) , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΣ ⟧ₙ) (⇒*-comp (red B⇒B'') (red D'') , ⟦ BΠ ⟧ₙ)
-- RedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              | ()
-- RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΠ ⟧ₙ) (⇒*-comp (red B⇒B'') (red D'') , ⟦ BΣ ⟧ₙ)
-- RedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              | ()
-- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* ((red D) , ⟦ W ⟧ₙ) (⇒*-comp (red B⇒B'') (red D₁) , ne neK)))
-- RedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( ⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))


-- -- Neutrals
-- RedShapeView (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whrDet* (red A⇒A'' , Uₙ) (red D , ne neK)
-- RedShapeView (ne (ne K D () K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl 
-- RedShapeView (ne (ne K D neK K≡K) neB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red ℕA) , ℕₙ) (red D , ne neK)))
-- RedShapeView (ne (ne K D neK K≡K) neB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red 𝔹A) , 𝔹ₙ) (red D , ne neK)))
-- -- RedShapeView (ne (ne K D neK K≡K) neB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red EmptyA) , Emptyₙ) (red D , ne neK)))
-- -- RedShapeView (ne (ne K D neK K≡K) neB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* (⇒*-comp (red A⇒A'') (red UnitA) , Unitₙ) (red D , ne neK)))
-- RedShapeView (ne (ne K D neK K≡K) neB) (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* (⇒*-comp (red A⇒A'') (red D') , ⟦ W ⟧ₙ) (red D , ne neK)))
-- RedShapeView (ne (ne K D neK K≡K) neB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA')))

-- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
--   with whrDet* (red B⇒B'' , Uₙ) (red D , ne neK)
-- RedShapeView (ne neA (ne K D () K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
--   | PE.refl 
-- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red ℕB) , ℕₙ) (red D , ne neK)))
-- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red 𝔹B) , 𝔹ₙ) (red D , ne neK)))
-- -- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red EmptyB) , Emptyₙ) (red D , ne neK)))
-- -- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* (⇒*-comp (red B⇒B'') (red UnitB) , Unitₙ) (red D , ne neK)))
-- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Bᵣ′ W F G D'' ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* (⇒*-comp (red B⇒B'') (red D'') , ⟦ W ⟧ₙ) (red D , ne neK)))
-- RedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) (⇒*-comp (red B⇒B'') (red A⇒A') , αₙ αA')))

-- -- αNeutrals
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (U≢αne αA (whrDet* (red A⇒A'' , Uₙ) (red A⇒A' , αₙ αA)))
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αA (whrDet* (red ℕA , ℕₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αA (whrDet* (red 𝔹A , 𝔹ₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
-- -- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵣ D) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αA (whrDet* (red D , Emptyₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
-- -- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵣ D) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA (whrDet* (red D , Unitₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))
-- RedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne′ K D₁ neK K≡K) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA (whrDet* (red D₁ , ne neK) (whrDet↘ (red A⇒A' , αₙ αA) (red A⇒A'') , αₙ αA)))

-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Uᵣ UB) A⇒A'' B⇒B'' =
--   ⊥-elim (U≢αne αB (whrDet* (red B⇒B'' , Uₙ) (red B⇒B' , αₙ αB)))
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αB (whrDet* (red ℕB , ℕₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αB (whrDet* (red 𝔹B , 𝔹ₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
-- -- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Emptyᵣ D) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αB (whrDet* (red D , Emptyₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
-- -- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Unitᵣ D) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢αne αB (whrDet* (red D , Unitₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))
-- RedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αB (whrDet* (red D₁ , ne neK) (whrDet↘ (red B⇒B' , αₙ αB) (red B⇒B'') , αₙ αB)))



-- AntiRedShapeView : ∀ {A A' B B' k k' k'' k'''} {[A]' : Γ / lε ⊩⟨ k ⟩ A'} {[B]' : Γ / lε ⊩⟨ k' ⟩ B'}
--                                       ([AB]' : ShapeView Γ k k' A' B' [A]' [B]')
--                                       ([A] : Γ / lε ⊩⟨ k'' ⟩ A) ([B] : Γ / lε ⊩⟨ k''' ⟩ B)
--                                       (A⇒A' : Γ / lε ⊢ A :⇒*: A') (B⇒B' : Γ / lε ⊢ B :⇒*: B')
--                                       → ShapeView Γ k'' k''' A B [A] [B]
-- -- The case of U
-- AntiRedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   with redU* (red A⇒U) with redU* (red B⇒U)
-- AntiRedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   | PE.refl | PE.refl with TyLogU [A]' with TyLogU [B]' 
-- AntiRedShapeView (Uᵥ UA UB) [A]' [B]' A⇒U B⇒U
--   | PE.refl | PE.refl | UA' , PE.refl | UB' , PE.refl = Uᵥ UA' UB'

-- -- Diagonal cases
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ℕᵣ ℕB) A⇒A'' B⇒B'' = ℕᵥ ℕA ℕB
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' = 𝔹ᵥ 𝔹A 𝔹B
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A⇒A'' B⇒B'' = Emptyᵥ EmptyA EmptyB
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Unitᵣ UnitB) A⇒A'' B⇒B'' = Unitᵥ UnitA UnitB
-- AntiRedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
--   Bᵥ BΠ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
-- AntiRedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B'' =
--   Bᵥ BΣ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
-- AntiRedShapeView (ne neA neB) (ne neA') (ne neB') A⇒A'' B⇒B'' = ne neA' neB'
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   with whrDet* (red A⇒A' , αₙ αA) ( whrDet↘ (red A⇒A'' , αₙ αA') (red A⇒A′) , αₙ αA')
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl with αNeutralHProp αA αA'
-- AntiRedShapeView (ϝᵣ-l {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] A⇒A′ B⇒B''
--   | PE.refl | PE.refl | PE.refl = ϝᵣ-l A⇒A'' αA' [B'] tA fA _ _
--     (AntiRedShapeView tAB tA (τTyLog [B']) (τwfRed* A⇒A′) (τwfRed* B⇒B''))
--     (AntiRedShapeView fAB fA (τTyLog [B']) (τwfRed* A⇒A′) (τwfRed* B⇒B''))
-- --  ϝᵣ-l A⇒A'' αA' [B'] tA fA _ _ ? ?
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   with whrDet* (red B⇒B' , αₙ αB) ( whrDet↘ (red B⇒B'' , αₙ αB') (red B⇒B′) , αₙ αB')
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl with αNeutralHProp αB αB'
-- AntiRedShapeView (ϝᵣ-r {nε = nε} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) A⇒A'' B⇒B′
--   | PE.refl | PE.refl | PE.refl =
--   ϝᵣ-r B⇒B'' αB' [A'] _ _ tB fB
--   (AntiRedShapeView tAB (τTyLog [A']) tB (τwfRed* A⇒A'') (τwfRed* B⇒B′))
--   (AntiRedShapeView fAB (τTyLog [A']) fB (τwfRed* A⇒A'') (τwfRed* B⇒B′))

-- -- Embeddings
-- AntiRedShapeView (emb⁰¹ [AB]) = AntiRedShapeView [AB]
-- AntiRedShapeView (emb¹⁰ [AB]) = AntiRedShapeView [AB]
-- AntiRedShapeView [AB] (emb 0<1 [A]) [B] A⇒A'' B⇒B′ = emb⁰¹ (AntiRedShapeView [AB] [A] [B] A⇒A'' B⇒B′)
-- AntiRedShapeView [AB] [A] (emb 0<1 [B]) A⇒A'' B⇒B′ = emb¹⁰ (AntiRedShapeView [AB] [A] [B] A⇒A'' B⇒B′)


-- -- ℕ
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whnfRed* (red A⇒A'') Uₙ 
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl with whrDet* ( red (idRed:*: (⊢A-red ℕA')) , Uₙ) (red ℕA' , ℕₙ)
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl | ()
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' 
--   with whrDet* ( whrDet↘ (red 𝔹A , 𝔹ₙ) (red A⇒A'') , 𝔹ₙ) (red ℕA' , ℕₙ)
-- ... | ()
-- -- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* ( whrDet↘ (red EmptyA , Emptyₙ) (red A⇒A'') , Emptyₙ) (red ℕA' , ℕₙ)
-- -- ... | ()
-- -- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red UnitA , Unitₙ) (red A⇒A'') , Unitₙ) (red ℕA' , ℕₙ)
-- -- ... | ()
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕA' , ℕₙ) ( whrDet↘ (red D' , ⟦ W ⟧ₙ) (red A⇒A'') , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕA') , ℕₙ) ( whrDet↘ (red D , ne neK) (red A⇒A'') , ne neK)))
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕA' , ℕₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))

-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
--   with whrDet* ( id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red ℕB') , ℕₙ)
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) A⇒A'' B⇒B''
--   | ()
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (𝔹ᵣ D) A⇒A'' B⇒B''
--   with whrDet* ( whrDet↘ (red D , 𝔹ₙ) (red B⇒B'') , 𝔹ₙ) (red ℕB' , ℕₙ)
-- ... | ()
-- -- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Emptyᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red D , Emptyₙ) (red B⇒B'') , Emptyₙ) (red ℕB' , ℕₙ)
-- -- ... | ()
-- -- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Unitᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red D , Unitₙ) (red B⇒B'') , Unitₙ) (red ℕB' , ℕₙ)
-- -- ... | ()
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢B W (whrDet* (red ℕB' , ℕₙ) ( whrDet↘ (red D , ⟦ W ⟧ₙ) (red B⇒B'') , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red ℕB') , ℕₙ) ( whrDet↘ (red D , ne neK) (red B⇒B'') , ne neK)))
-- AntiRedShapeView (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = 
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red ℕB' , ℕₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))

-- -- ℕ
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whnfRed* (red A⇒A'') Uₙ 
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl with whrDet* ( red (idRed:*: (⊢A-red 𝔹A')) , Uₙ) (red 𝔹A' , 𝔹ₙ)
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl | ()
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' 
--   with whrDet* ( whrDet↘ (red ℕA , ℕₙ) (red A⇒A'') , ℕₙ) (red 𝔹A' , 𝔹ₙ)
-- ... | ()
-- -- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* ( whrDet↘ (red EmptyA , Emptyₙ) (red A⇒A'') , Emptyₙ) (red 𝔹A' , 𝔹ₙ)
-- -- ... | ()
-- -- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red UnitA , Unitₙ) (red A⇒A'') , Unitₙ) (red 𝔹A' , 𝔹ₙ)
-- -- ... | ()
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹A' , 𝔹ₙ) ( whrDet↘ (red D' , ⟦ W ⟧ₙ) (red A⇒A'') , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red 𝔹A') , 𝔹ₙ) ( whrDet↘ (red D , ne neK) (red A⇒A'') , ne neK)))
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red 𝔹A' , 𝔹ₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))

-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB) A⇒A'' B⇒B''
--   with whrDet* ( id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red 𝔹B') , 𝔹ₙ)
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB) A⇒A'' B⇒B''
--   | ()
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ℕᵣ D) A⇒A'' B⇒B''
--   with whrDet* ( whrDet↘ (red D , ℕₙ) (red B⇒B'') , ℕₙ) (red 𝔹B' , 𝔹ₙ)
-- ... | ()
-- -- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Emptyᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red D , Emptyₙ) (red B⇒B'') , Emptyₙ) (red 𝔹B' , 𝔹ₙ)
-- -- ... | ()
-- -- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Unitᵣ D) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red D , Unitₙ) (red B⇒B'') , Unitₙ) (red 𝔹B' , 𝔹ₙ)
-- -- ... | ()
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹B' , 𝔹ₙ) ( whrDet↘ (red D , ⟦ W ⟧ₙ) (red B⇒B'') , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ne′ K D neK K≡K) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red 𝔹B') , 𝔹ₙ) ( whrDet↘ (red D , ne neK) (red B⇒B'') , ne neK)))
-- AntiRedShapeView (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' = 
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red 𝔹B' , 𝔹ₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))


-- -- -- Empty
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Uᵣ UA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* ( id (escape (Uᵣ UA)) , Uₙ) (⇒*-comp (red A⇒A'') (red EmptyA') , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' 
-- --   with whrDet* ( whrDet↘ (red ℕA , ℕₙ) (red A⇒A'') , ℕₙ) (red EmptyA' , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Unitᵣ UnitA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red UnitA , Unitₙ) (red A⇒A'') , Unitₙ) (red EmptyA' , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢B W (whrDet* (red EmptyA' , Emptyₙ) ( whrDet↘ (red D' , ⟦ W ⟧ₙ) (red A⇒A'') , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyA') , Emptyₙ) ( whrDet↘ (red D , ne neK) (red A⇒A'') , ne neK)))
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' = 
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyA' , Emptyₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))

-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Uᵣ UB) A⇒A'' B⇒B''
-- --   with whrDet* ( id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red EmptyB') , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ℕᵣ ℕB) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red ℕB , ℕₙ) (red B⇒B'') , ℕₙ) (red EmptyB' , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Unitᵣ UnitB) A⇒A'' B⇒B''
-- --   with whrDet* ( whrDet↘ (red UnitB , Unitₙ) (red B⇒B'') , Unitₙ) (red EmptyB' , Emptyₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyB' , Emptyₙ) ( whrDet↘ (red D , ⟦ W ⟧ₙ) (red B⇒B'') , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red EmptyB') , Emptyₙ) ( whrDet↘ (red D , ne neK) (red B⇒B'') , ne neK)))
-- -- AntiRedShapeView (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red EmptyB' , Emptyₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))


-- -- -- Unit
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB')  (Uᵣ UA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* ( id (escape (Uᵣ UA)) , Uₙ) (⇒*-comp (red A⇒A'') (red UnitA') , Unitₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (ℕᵣ ℕA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red UnitA' , Unitₙ) ( whrDet↘ (red ℕA , ℕₙ) (red A⇒A'') , ℕₙ) 
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B''
-- --   with whrDet* (red UnitA' , Unitₙ) ( whrDet↘ (red EmptyA , Emptyₙ) (red A⇒A'') , Emptyₙ) 
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' = 
-- --  ⊥-elim (Unit≢B W (whrDet* (red UnitA' , Unitₙ) ( whrDet↘ (red D' , ⟦ W ⟧ₙ) (red A⇒A'') , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (ne′ K D neK K≡K) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red UnitA') , Unitₙ) ( whrDet↘ (red D , ne neK) (red A⇒A'') , ne neK)))
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red UnitA' , Unitₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))

-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Uᵣ UB) A⇒A'' B⇒B''
-- --   with whrDet* ( id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red UnitB') , Unitₙ)
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ℕᵣ ℕB) A⇒A'' B⇒B''
-- --   with whrDet* (red UnitB' , Unitₙ) ( whrDet↘ (red ℕB , ℕₙ) (red B⇒B'') , ℕₙ) 
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Emptyᵣ D) A⇒A'' B⇒B'' 
-- --   with whrDet* (red UnitB' , Unitₙ) ( whrDet↘ (red D , Emptyₙ) (red B⇒B'') , Emptyₙ) 
-- -- ... | ()
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* (red UnitB' , Unitₙ) ( whrDet↘ (red D , ⟦ W ⟧ₙ) (red B⇒B'') , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ne′ K D neK K≡K) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red UnitB') , Unitₙ) ( whrDet↘ (red D , ne neK) (red B⇒B'') , ne neK)))
-- -- AntiRedShapeView (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red UnitB' , Unitₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))


-- -- Σ and Π-types
-- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (U≢B W (whrDet* (id (escape (Uᵣ UA)) , Uₙ) (⇒*-comp (red A⇒A'') (red D) , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A] (Uᵣ UB) A⇒A'' B⇒B'' =
--   ⊥-elim (U≢B W (whrDet* (id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red D) , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' = 
--  ⊥-elim (ℕ≢B W (whrDet* ( whrDet↘ (red ℕA , ℕₙ) (red A⇒A'') , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' = 
--  ⊥-elim (𝔹≢B W (whrDet* ( whrDet↘ (red 𝔹A , 𝔹ₙ) (red A⇒A'') , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢B W (whrDet* ( whrDet↘ (red EmptyA , Emptyₙ) (red A⇒A'') , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* ( whrDet↘ (red UnitA , Unitₙ) (red A⇒A'') , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ne′ K' D' neK' K≡K') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK' (whrDet* ((red D) , ⟦ W ⟧ₙ) ( whrDet↘ (red D' , ne neK') (red A⇒A'') , ne neK')))
-- AntiRedShapeView (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))
-- AntiRedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' 
--              with whrDet* (red D , ⟦ BΠ ⟧ₙ) ( whrDet↘ (red D' , Σₙ) (red A⇒A'') , ⟦ BΣ ⟧ₙ)
-- AntiRedShapeView (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              | ()
-- AntiRedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΣ ⟧ₙ) ( whrDet↘ (red D' , Πₙ) (red A⇒A'') , ⟦ BΠ ⟧ₙ)
-- AntiRedShapeView (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B''
--              | ()


-- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--  ⊥-elim (ℕ≢B W (whrDet* ( whrDet↘ (red ℕB , ℕₙ) (red B⇒B'') , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--  ⊥-elim (𝔹≢B W (whrDet* ( whrDet↘ (red 𝔹B , 𝔹ₙ) (red B⇒B'') , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Empty≢B W (whrDet* ( whrDet↘ (red EmptyB , Emptyₙ) (red B⇒B'') , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
-- --  ⊥-elim (Unit≢B W (whrDet* ( whrDet↘ (red UnitB , Unitₙ) (red B⇒B'') , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- AntiRedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΣ ⟧ₙ) ( whrDet↘ (red D'' , Πₙ) (red B⇒B'') , ⟦ BΠ ⟧ₙ)
-- AntiRedShapeView (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              | ()
-- AntiRedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              with whrDet* (red D , ⟦ BΠ ⟧ₙ) ( whrDet↘ (red D'' , Σₙ) (red B⇒B'') , ⟦ BΣ ⟧ₙ)
-- AntiRedShapeView (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') A⇒A'' B⇒B''
--              | ()
-- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* ((red D) , ⟦ W ⟧ₙ) ( whrDet↘ (red D₁ , ne neK) (red B⇒B'') , ne neK)))
-- AntiRedShapeView (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA' (whrDet* (red D , ⟦ W ⟧ₙ) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))


-- -- Neutrals
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   with whnfRed* (red A⇒A'') Uₙ
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl with whrDet* ( id (⊢A-red D) , Uₙ) (red D , ne neK)
-- AntiRedShapeView (ne (ne K D () K≡K) neB) (Uᵣ UA) [B'] A⇒A'' B⇒B''
--   | PE.refl | PE.refl
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢ne neK (whrDet* ( whrDet↘ (red ℕA , ℕₙ) (red A⇒A'') , ℕₙ) (red D , ne neK)))
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢ne neK (whrDet* ( whrDet↘ (red 𝔹A , 𝔹ₙ) (red A⇒A'') , 𝔹ₙ) (red D , ne neK)))
-- -- AntiRedShapeView (ne (ne K D neK K≡K) neB) (Emptyᵣ EmptyA) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ( whrDet↘ (red EmptyA , Emptyₙ) (red A⇒A'') , Emptyₙ) (red D , ne neK)))
-- -- AntiRedShapeView (ne (ne K D neK K≡K) neB) (Unitᵣ UnitA) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ( whrDet↘ (red UnitA , Unitₙ) (red A⇒A'') , Unitₙ) (red D , ne neK)))
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* ( whrDet↘ (red D' , ⟦ W ⟧ₙ) (red A⇒A'') , ⟦ W ⟧ₙ) (red D , ne neK)))
-- AntiRedShapeView (ne (ne K D neK K≡K) neB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) ( whrDet↘ (red A⇒A' , αₙ αA') (red A⇒A'') , αₙ αA')))

-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
--   with whnfRed* (red B⇒B'') Uₙ
-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
--   | PE.refl with whrDet* (id (⊢A-red D) , Uₙ) (red D , ne neK)
-- AntiRedShapeView (ne neA (ne K D () K≡K)) (ne neA') (Uᵣ UB) A⇒A'' B⇒B''
--   | PE.refl | PE.refl 
-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢ne neK (whrDet* ( whrDet↘ (red ℕB , ℕₙ) (red B⇒B'') , ℕₙ) (red D , ne neK)))
-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢ne neK (whrDet* ( whrDet↘ (red 𝔹B , 𝔹ₙ) (red B⇒B'') , 𝔹ₙ) (red D , ne neK)))
-- -- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Emptyᵣ EmptyB) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ( whrDet↘ (red EmptyB , Emptyₙ) (red B⇒B'') , Emptyₙ) (red D , ne neK)))
-- -- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Unitᵣ UnitB) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ( whrDet↘ (red UnitB , Unitₙ) (red B⇒B'') , Unitₙ) (red D , ne neK)))
-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (Bᵣ′ W F G D'' ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢ne W neK (whrDet* ( whrDet↘ (red D'' , ⟦ W ⟧ₙ) (red B⇒B'') , ⟦ W ⟧ₙ) (red D , ne neK)))
-- AntiRedShapeView (ne neA (ne K D neK K≡K)) (ne neA') (ϝᵣ mε A⇒A' αA' tA fA) A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red D , ne neK) ( whrDet↘ (red A⇒A' , αₙ αA') (red B⇒B'') , αₙ αA')))

-- -- αNeutrals
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Uᵣ UA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (U≢αne αA (whrDet* ( id (escape (Uᵣ UA)) , Uₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵣ ℕA) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αA (whrDet* (red ℕA , ℕₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (𝔹ᵣ 𝔹A) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αA (whrDet* (red 𝔹A , 𝔹ₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- -- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵣ D) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αA (whrDet* (red D , Emptyₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- -- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵣ D) [B'] A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αA (whrDet* (red D , Unitₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))
-- AntiRedShapeView (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne′ K D₁ neK K≡K) [B'] A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αA (whrDet* (red D₁ , ne neK) (⇒*-comp (red A⇒A'') (red A⇒A') , αₙ αA)))

-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Uᵣ UB) A⇒A'' B⇒B'' =
--   ⊥-elim (U≢αne αB (whrDet* ( id (escape (Uᵣ UB)) , Uₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ℕᵣ ℕB) A⇒A'' B⇒B'' =
--   ⊥-elim (ℕ≢αne αB (whrDet* (red ℕB , ℕₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (𝔹ᵣ 𝔹B) A⇒A'' B⇒B'' =
--   ⊥-elim (𝔹≢αne αB (whrDet* (red 𝔹B , 𝔹ₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- -- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Emptyᵣ D) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Empty≢αne αB (whrDet* (red D , Emptyₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- -- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Unitᵣ D) A⇒A'' B⇒B'' =
-- --   ⊥-elim (Unit≢αne αB (whrDet* (red D , Unitₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) A⇒A'' B⇒B'' =
--   ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))
-- AntiRedShapeView (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ne′ K D₁ neK K≡K) A⇒A'' B⇒B'' =
--   ⊥-elim (ne≢αne neK αB (whrDet* (red D₁ , ne neK) (⇒*-comp (red B⇒B'') (red B⇒B') , αₙ αB)))



-- ShapeView≤W : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
--                       {WA WB} {BA : Γ / lε ⊩′⟨ k ⟩B⟨ WA ⟩ A}  {BB : Γ / lε ⊩′⟨ k′ ⟩B⟨ WB ⟩ B}
--                       ([AB] : ShapeView Γ k k′ A B (Bᵣ WA BA) (Bᵣ WB BB))
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
--                       (≤ε : l ≤ₗ l')
--                       → ShapeView Γ j j' A B [A]' [B]'
-- ShapeView≤W [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤W [AB] [A] [B] f<)
-- ShapeView≤W [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤W [AB] [A] [B] f<)

-- -- Diagonal cases
-- ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') f< =
--   Bᵥ BΠ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') 
-- ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'') f< =
--   Bᵥ BΣ (Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') (Bᵣ F'' G'' D'' ⊢F'' ⊢G'' A≡A'' [F''] [G''] G-ext'')
-- -- Σ and Π-types
-- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Uᵣ UA) [B'] f< =
--   ⊥-elim (U≢B W (whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A] (Uᵣ UB) f< =
--   ⊥-elim (U≢B W (whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ℕᵣ ℕA) [B'] f< = 
--  ⊥-elim (ℕ≢B W (whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (𝔹ᵣ 𝔹A) [B'] f< = 
--  ⊥-elim (𝔹≢B W (whrDet* ( (red 𝔹A) , 𝔹ₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- -- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Emptyᵣ EmptyA) [B'] f< =
-- --  ⊥-elim (Empty≢B W (whrDet* ( (red EmptyA) , Emptyₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- -- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (Unitᵣ UnitA) [B'] f< =
-- --  ⊥-elim (Unit≢B W (whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ne′ K' D' neK' K≡K') [B'] f< =
--   ⊥-elim (B≢ne W neK' (whrDet* ((red (wfRed≤* f< D) ) , ⟦ W ⟧ₙ) ( (red D') , ne neK')))
-- ShapeView≤W (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
--   ⊥-elim (B≢αne W αA' (whrDet* (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ) (  (red A⇒A') , αₙ αA')))
-- ShapeView≤W (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<  
--              with whrDet* (red (wfRed≤* f< D)  , ⟦ BΠ ⟧ₙ) ( (red D') , ⟦ BΣ ⟧ₙ)
-- ShapeView≤W (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
--              | ()
-- ShapeView≤W (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
--              with whrDet* (red (wfRed≤* f< D)  , ⟦ BΣ ⟧ₙ) ( (red D') , ⟦ BΠ ⟧ₙ)
-- ShapeView≤W (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB)
--              (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f<
--              | ()
-- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ℕᵣ ℕB) f< =
--  ⊥-elim (ℕ≢B W (whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (𝔹ᵣ 𝔹B) f< =
--  ⊥-elim (𝔹≢B W (whrDet* ( (red 𝔹B) , 𝔹ₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- -- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Emptyᵣ EmptyB) f< =
-- --  ⊥-elim (Empty≢B W (whrDet* ( (red EmptyB) , Emptyₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- -- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (Unitᵣ UnitB) f< =
-- --  ⊥-elim (Unit≢B W (whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ)))
-- ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f< 
--              with whrDet* (red (wfRed≤* f< D)  , ⟦ BΣ ⟧ₙ) ( (red D'') , ⟦ BΠ ⟧ₙ)
-- ShapeView≤W (Bᵥ BΣ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΣ BA')
--              (Bᵣ′ BΠ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
--              | ()
-- ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
--              with whrDet* (red (wfRed≤* f< D)  , ⟦ BΠ ⟧ₙ) ( (red D'') , ⟦ BΣ ⟧ₙ)
-- ShapeView≤W (Bᵥ BΠ BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ BΠ BA')
--              (Bᵣ′ BΣ F'' G'' D'' ⊢F'' ⊢G''w A≡A'' [F''] [G''] G-ext'') f<
--              | ()
-- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ne′ K D₁ neK K≡K) f< =
--   ⊥-elim (B≢ne W neK (whrDet* ((red (wfRed≤* f< D) ) , ⟦ W ⟧ₙ) ( (red D₁) , ne neK)))
-- ShapeView≤W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵣ W' BA') (ϝᵣ mε A⇒A' αA' tA fA) f< =
--   ⊥-elim (B≢αne W αA' (whrDet* (red (wfRed≤* f< D)  , ⟦ W ⟧ₙ) (  (red A⇒A') , αₙ αA')))

-- ShapeView≤ne : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
--                       {neA neB}
--                       ([AB] : ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB))
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
--                       (≤ε : l ≤ₗ l')
--                       → ShapeView Γ j j' A B [A]' [B]'
-- -- Diagonal case
-- ShapeView≤ne (ne neA neB) (ne neA') (ne neB') f< = ne neA' neB'
-- -- Embeddings
-- ShapeView≤ne [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ne [AB] [A] [B] f<)
-- ShapeView≤ne [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ne [AB] [A] [B] f<)
-- -- Impossible cases
-- ShapeView≤ne (ne (ne K D neK K≡K) neB) (Uᵣ UA) [B'] f<
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< D)  , ne neK)
-- ShapeView≤ne (ne (ne K D () K≡K) neB) (Uᵣ UA) [B'] f<
--   | PE.refl 
-- ShapeView≤ne (ne (ne K D neK K≡K) neB) (ℕᵣ ℕA) [B'] f< =
--   ⊥-elim (ℕ≢ne neK (whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne (ne K D neK K≡K) neB) (𝔹ᵣ 𝔹A) [B'] f< =
--   ⊥-elim (𝔹≢ne neK (whrDet* ( (red 𝔹A) , 𝔹ₙ) (red (wfRed≤* f< D)  , ne neK)))
-- -- ShapeView≤ne (ne (ne K D neK K≡K) neB) (Emptyᵣ EmptyA) [B'] f< =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ( (red EmptyA) , Emptyₙ) (red (wfRed≤* f< D)  , ne neK)))
-- -- ShapeView≤ne (ne (ne K D neK K≡K) neB) (Unitᵣ UnitA) [B'] f< =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne (ne K D neK K≡K) neB) (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
--   ⊥-elim (B≢ne W neK (whrDet* ( (red D') , ⟦ W ⟧ₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne (ne K D neK K≡K) neB) (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red (wfRed≤* f< D)  , ne neK) ( (red A⇒A') , αₙ αA')))

-- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Uᵣ UB) f< 
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< D)  , ne neK)
-- ShapeView≤ne (ne neA (ne K D () K≡K)) (ne neA') (Uᵣ UB) f<
--   | PE.refl 
-- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (ℕᵣ ℕB) f< =
--   ⊥-elim (ℕ≢ne neK (whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (𝔹ᵣ 𝔹B) f< =
--   ⊥-elim (𝔹≢ne neK (whrDet* ( (red 𝔹B) , 𝔹ₙ) (red (wfRed≤* f< D)  , ne neK)))
-- -- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Emptyᵣ EmptyB) f< =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ( (red EmptyB) , Emptyₙ) (red (wfRed≤* f< D)  , ne neK)))
-- -- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Unitᵣ UnitB) f< =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (Bᵣ′ W F G D'' ⊢F ⊢G A≡A [F] [G] G-ext) f< =
--   ⊥-elim (B≢ne W neK (whrDet* ( (red D'') , ⟦ W ⟧ₙ) (red (wfRed≤* f< D)  , ne neK)))
-- ShapeView≤ne (ne neA (ne K D neK K≡K)) (ne neA') (ϝᵣ mε A⇒A' αA' tA fA) f< =
--   ⊥-elim (ne≢αne neK αA' (whrDet* (red (wfRed≤* f< D)  , ne neK) ( (red A⇒A') , αₙ αA')))

-- ShapeView≤ℕ : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
--                       {ℕA ℕB}
--                       ([AB] : ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB))
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
--                       (≤ε : l ≤ₗ l')
--                       → ShapeView Γ j j' A B [A]' [B]'
-- -- Diagonal case
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ℕᵣ ℕB) f< = ℕᵥ ℕA ℕB
-- -- Embeddings
-- ShapeView≤ℕ [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ℕ [AB] [A] [B] f<)
-- ShapeView≤ℕ [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ℕ [AB] [A] [B] f<)
-- -- Impossible cases
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] f< 
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< ℕA') , ℕₙ)
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Uᵣ UA) [B'] f<
--   | ()
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (𝔹ᵣ 𝔹A) [B'] f<
--   with whrDet* ( red 𝔹A , 𝔹ₙ) (red (wfRed≤* f< ℕA') , ℕₙ)
-- ... | ()
-- -- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Emptyᵣ EmptyA) [B'] f<
-- --   with whrDet* ( red EmptyA , Emptyₙ) (red (wfRed≤* f< ℕA') , ℕₙ)
-- -- ... | ()
-- -- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Unitᵣ UnitA) [B'] f<
-- --   with whrDet* ( (red UnitA) , Unitₙ) (red ( wfRed≤* f< ℕA') , ℕₙ)
-- -- ... | ()
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
--   ⊥-elim (ℕ≢B W (whrDet* (red (wfRed≤* f< ℕA') , ℕₙ) ( (red D') , ⟦ W ⟧ₙ)))
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ne′ K D neK K≡K) [B'] f< = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red (wfRed≤* f< ℕA') ) , ℕₙ) ( (red D) , ne neK)))
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red (wfRed≤* f< ℕA')  , ℕₙ) (  (red A⇒A') , αₙ αA')))

-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB)  f<
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Uᵣ UB) f<
--   | ()
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (𝔹ᵣ D) f< 
--   with whrDet* ( (red D) , 𝔹ₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
-- ... | ()
-- -- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Emptyᵣ D) f< 
-- --   with whrDet* ( (red D) , Emptyₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
-- -- ... | ()
-- -- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Unitᵣ D) f<
-- --   with whrDet* ( (red D) , Unitₙ) (red (wfRed≤* f< ℕB')  , ℕₙ)
-- -- ... | ()
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< = 
--   ⊥-elim (ℕ≢B W (whrDet* (red (wfRed≤* f< ℕB')  , ℕₙ) ( (red D) , ⟦ W ⟧ₙ)))
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ne′ K D neK K≡K) f< = 
--   ⊥-elim (ℕ≢ne neK (whrDet* ((red (wfRed≤* f< ℕB') ) , ℕₙ) ( (red D) , ne neK)))
-- ShapeView≤ℕ (ℕᵥ ℕA' ℕB') (ℕᵣ ℕA) (ϝᵣ mε A⇒A' αA' tA fA) f< = 
--   ⊥-elim (ℕ≢αne αA' (whrDet* (red (wfRed≤* f< ℕB')  , ℕₙ) (  (red A⇒A') , αₙ αA')))


-- ShapeView≤𝔹 : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
--                       {𝔹A 𝔹B}
--                       ([AB] : ShapeView Γ {l} {lε} k k′ A B (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B))
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
--                       (≤ε : l ≤ₗ l')
--                       → ShapeView Γ j j' A B [A]' [B]'
-- -- Diagonal case
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) f< = 𝔹ᵥ 𝔹A 𝔹B
-- -- Embeddings
-- ShapeView≤𝔹 [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤𝔹 [AB] [A] [B] f<)
-- ShapeView≤𝔹 [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤𝔹 [AB] [A] [B] f<)
-- -- Impossible cases
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] f< 
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< 𝔹A') , 𝔹ₙ)
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (Uᵣ UA) [B'] f<
--   | ()
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (ℕᵣ ℕA) [B'] f<
--   with whrDet* ( red ℕA , ℕₙ) (red (wfRed≤* f< 𝔹A') , 𝔹ₙ)
-- ... | ()
-- -- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (Emptyᵣ EmptyA) [B'] f<
-- --   with whrDet* ( red EmptyA , Emptyₙ) (red (wfRed≤* f< 𝔹A') , 𝔹ₙ)
-- -- ... | ()
-- -- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (Unitᵣ UnitA) [B'] f<
-- --   with whrDet* ( (red UnitA) , Unitₙ) (red ( wfRed≤* f< 𝔹A') , 𝔹ₙ)
-- -- ... | ()
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
--   ⊥-elim (𝔹≢B W (whrDet* (red (wfRed≤* f< 𝔹A') , 𝔹ₙ) ( (red D') , ⟦ W ⟧ₙ)))
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (ne′ K D neK K≡K) [B'] f< = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red (wfRed≤* f< 𝔹A') ) , 𝔹ₙ) ( (red D) , ne neK)))
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red (wfRed≤* f< 𝔹A')  , 𝔹ₙ) (  (red A⇒A') , αₙ αA')))

-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB)  f<
--   with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ)
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Uᵣ UB) f<
--   | ()
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ℕᵣ D) f< 
--   with whrDet* ( (red D) , ℕₙ) (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ)
-- ... | ()
-- -- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Emptyᵣ D) f< 
-- --   with whrDet* ( (red D) , Emptyₙ) (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ)
-- -- ... | ()
-- -- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Unitᵣ D) f<
-- --   with whrDet* ( (red D) , Unitₙ) (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ)
-- -- ... | ()
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< = 
--   ⊥-elim (𝔹≢B W (whrDet* (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ) ( (red D) , ⟦ W ⟧ₙ)))
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ne′ K D neK K≡K) f< = 
--   ⊥-elim (𝔹≢ne neK (whrDet* ((red (wfRed≤* f< 𝔹B') ) , 𝔹ₙ) ( (red D) , ne neK)))
-- ShapeView≤𝔹 (𝔹ᵥ 𝔹A' 𝔹B') (𝔹ᵣ 𝔹A) (ϝᵣ mε A⇒A' αA' tA fA) f< = 
--   ⊥-elim (𝔹≢αne αA' (whrDet* (red (wfRed≤* f< 𝔹B')  , 𝔹ₙ) (  (red A⇒A') , αₙ αA')))


-- -- ShapeView≤Empty : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
-- --                       {EmptyA EmptyB}
-- --                       ([AB] : ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EmptyA) (Emptyᵣ EmptyB))
-- --                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
-- --                       (≤ε : l ≤ₗ l')
-- --                       → ShapeView Γ j j' A B [A]' [B]'
-- -- -- Diagonal case
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) f< = Emptyᵥ EmptyA EmptyB
-- -- -- Embeddings
-- -- ShapeView≤Empty [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤Empty [AB] [A] [B] f<)
-- -- ShapeView≤Empty [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤Empty [AB] [A] [B] f<)
-- -- -- Impossible cases
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Uᵣ UA) [B'] f<
-- --   with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ℕᵣ ℕA) [B'] f<
-- --   with whrDet* ( (red ℕA) , ℕₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Unitᵣ UnitA) [B'] f< 
-- --   with whrDet* ( (red UnitA) , Unitₙ) (red (wfRed≤* f< EmptyA')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< =
-- --  ⊥-elim (Empty≢B W (whrDet* (red (wfRed≤* f< EmptyA')  , Emptyₙ) ( (red D') , ⟦ W ⟧ₙ)))
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ne′ K D neK K≡K) [B'] f< =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red (wfRed≤* f< EmptyA') ) , Emptyₙ) ( (red D) , ne neK)))
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< = 
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red (wfRed≤* f< EmptyA')  , Emptyₙ) (  (red A⇒A') , αₙ αA')))

-- -- ShapeView≤Empty {lε' = lε'} (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Uᵣ UB) f<
-- --   with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ℕᵣ ℕB) f<
-- --   with whrDet* ( (red ℕB) , ℕₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Unitᵣ UnitB) f<
-- --   with whrDet* ( (red UnitB) , Unitₙ) (red (wfRed≤* f< EmptyB')  , Emptyₙ)
-- -- ... | ()
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< =
-- --   ⊥-elim (Empty≢B W (whrDet* (red (wfRed≤* f< EmptyB')  , Emptyₙ) ( (red D) , ⟦ W ⟧ₙ)))
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ne′ K D neK K≡K) f< =
-- --   ⊥-elim (Empty≢ne neK (whrDet* ((red (wfRed≤* f< EmptyB') ) , Emptyₙ) ( (red D) , ne neK)))
-- -- ShapeView≤Empty (Emptyᵥ EmptyA' EmptyB') (Emptyᵣ EmptyA) (ϝᵣ mε A⇒A' αA' tA fA) f< =
-- --   ⊥-elim (Empty≢αne αA' (whrDet* (red (wfRed≤* f< EmptyB')  , Emptyₙ) (  (red A⇒A') , αₙ αA')))

-- -- ShapeView≤Unit : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
-- --                       {UnitA UnitB}
-- --                       ([AB] : ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB))
-- --                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
-- --                       (≤ε : l ≤ₗ l')
-- --                       → ShapeView Γ j j' A B [A]' [B]'
-- -- -- Diagonal case
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Unitᵣ UnitB) f< = Unitᵥ UnitA UnitB
-- -- -- Embeddings
-- -- ShapeView≤Unit [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤Unit [AB] [A] [B] f<)
-- -- ShapeView≤Unit [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤Unit [AB] [A] [B] f<)
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB')  (Uᵣ UA) [B']  f<
-- --   with whrDet* ( red (idRed:*: (escape (Uᵣ UA))) , Uₙ) (red (wfRed≤* f< UnitA')  , Unitₙ)
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (ℕᵣ ℕA) [B'] f<
-- --   with whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red ℕA) , ℕₙ) 
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Emptyᵣ EmptyA) [B'] f<
-- --   with whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red EmptyA) , Emptyₙ) 
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') [B'] f< = 
-- --  ⊥-elim (Unit≢B W (whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) ( (red D') , ⟦ W ⟧ₙ)))
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (ne′ K D neK K≡K) [B'] f< =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red (wfRed≤* f< UnitA') ) , Unitₙ) ( (red D) , ne neK)))
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (ϝᵣ mε A⇒A' αA' tA fA) [B'] f< =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red (wfRed≤* f< UnitA')  , Unitₙ) (  (red A⇒A') , αₙ αA')))

-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Uᵣ UB) f<
-- --   with whrDet* ( red (idRed:*: (escape (Uᵣ UB))) , Uₙ) (red (wfRed≤* f< UnitB')  , Unitₙ)
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ℕᵣ ℕB) f<
-- --   with whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red ℕB) , ℕₙ) 
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Emptyᵣ D) f<  
-- --   with whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red D) , Emptyₙ) 
-- -- ... | ()
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f< =
-- --  ⊥-elim (Unit≢B W (whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) ( (red D) , ⟦ W ⟧ₙ)))
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ne′ K D neK K≡K) f< =
-- --   ⊥-elim (Unit≢ne neK (whrDet* ((red (wfRed≤* f< UnitB') ) , Unitₙ) ( (red D) , ne neK)))
-- -- ShapeView≤Unit (Unitᵥ UnitA' UnitB') (Unitᵣ UnitA) (ϝᵣ mε A⇒A' αA' tA fA) f< =
-- --   ⊥-elim (Unit≢αne αA' (whrDet* (red (wfRed≤* f< UnitB')  , Unitₙ) (  (red A⇒A') , αₙ αA')))
  

-- ShapeView≤ : ∀ {k k′ j j'} {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
--                       {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
--                       ([AB] : ShapeView Γ k k′ A B [A] [B])
--                       ([A]' : Γ / lε' ⊩⟨ j ⟩ A) ([B]' : Γ / lε' ⊩⟨ j' ⟩ B)
--                       (≤ε : l ≤ₗ l')
--                       → ShapeView Γ j j' A B [A]' [B]'
-- -- U
-- ShapeView≤ (Uᵥ UA UB) [A'] [B'] f<
--   with TyLogU [A'] with TyLogU [B']
-- ShapeView≤ (Uᵥ UA UB) (Uᵣ UA') (Uᵣ UB') f<
--   | UA' , PE.refl | UB' , PE.refl = Uᵥ UA' UB'

-- -- Embeddings
-- ShapeView≤ (emb⁰¹ [AB]) [A'] [B'] f< = ShapeView≤ [AB] [A'] [B'] f<
-- ShapeView≤ (emb¹⁰ [AB]) [A'] [B'] f< = ShapeView≤ [AB] [A'] [B'] f<
-- ShapeView≤ [AB] (emb 0<1 [A]) [B] f< = emb⁰¹ (ShapeView≤ [AB] [A] [B] f<)
-- ShapeView≤ [AB] [A] (emb 0<1 [B]) f< = emb¹⁰ (ShapeView≤ [AB] [A] [B] f<)


-- -- ℕ
-- ShapeView≤ {k = k} {k′ = k′} (ℕᵥ ℕA' ℕB') [A'] [B'] f< =
--   ShapeView≤ℕ {k = k} {k′ = k′} (ℕᵥ ℕA' ℕB') [A'] [B'] f<

-- -- 𝔹
-- ShapeView≤ {k = k} {k′ = k′} (𝔹ᵥ 𝔹A' 𝔹B') [A'] [B'] f< =
--   ShapeView≤𝔹 {k = k} {k′ = k′} (𝔹ᵥ 𝔹A' 𝔹B') [A'] [B'] f<

-- -- -- Empty
-- -- ShapeView≤ {k = k} {k′ = k′} (Emptyᵥ EmptyA' EmptyB') [A'] [B'] f<
-- --   = ShapeView≤Empty {k = k} {k′ = k′} (Emptyᵥ EmptyA' EmptyB') [A'] [B'] f<

-- -- -- Unit
-- -- ShapeView≤ {k = k} {k′ = k′} (Unitᵥ UnitA' UnitB') [A'] [B'] f<
-- --   = ShapeView≤Unit {k = k} {k′ = k′} (Unitᵥ UnitA' UnitB') [A'] [B'] f<
  
-- -- Σ and Π-types
-- ShapeView≤ (Bᵥ W BA BB) [A'] [B'] f< =
--   ShapeView≤W (Bᵥ W BA BB) [A'] [B'] f<

-- -- Neutrals
-- ShapeView≤ {k = k} {k′ = k′} (ne neA neB) [A'] [B'] f< =
--   ShapeView≤ne {k = k} {k′ = k′} (ne neA neB) [A'] [B'] f<

-- -- Left αNeutrals
-- ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   with decidInLConNat l' n
-- ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   | TS.inj₁ (TS.inj₁ nε') =
--   ShapeView≤ tAB [A'] [B'] (≤ₗ-add _ _ _ f< nε')
-- ShapeView≤ {l' = l'} (ϝᵣ-l {n = n} {nε = nε} A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   | TS.inj₁ (TS.inj₂ nε') =
--   ShapeView≤ fAB [A'] [B'] (≤ₗ-add _ _ _ f< nε')
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ℕᵣ ℕA) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
--                     (whrDet* (red ℕA , ℕₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (𝔹ᵣ 𝔹A) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (𝔹≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
--                     (whrDet* (red 𝔹A , 𝔹ₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Uᵣ UA) [B'] f<
--   | TS.inj₂ notinl' = ⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
-- -- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Emptyᵣ D) [B'] f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
-- --                     (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- -- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Unitᵣ D) [B'] f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
-- --                    (whrDet* (red D , Unitₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αA)
--                     (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne′ K D₁ neK K≡K) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αA) (whrDet* (red D₁ , ne neK)
--                  (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- -- Special case of left αNeutrals with embeddings
-- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (ℕᵣ ℕA)) [B'] f<
--   | TS.inj₂ notinl' = 
--   ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
--                     (whrDet* (red ℕA , ℕₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (𝔹ᵣ 𝔹A)) [B'] f<
--   | TS.inj₂ notinl' = 
--   ⊥-elim (𝔹≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
--                     (whrDet* (red 𝔹A , 𝔹ₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- -- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (Emptyᵣ D)) [B'] f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
-- --                     (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- -- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (Unitᵣ D)) [B'] f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αA)
-- --                    (whrDet* (red D , Unitₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB)
--            (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αA)
--                     (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB)
--            (emb 0<1 (ne′ K D₁ neK K≡K)) [B'] f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αA) (whrDet* (red D₁ , ne neK)
--                  (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA))))
-- -- Embedding of diagonal left αNeutrals
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (ϝᵣ mε A⇒A'' αA' tA fA)) [B'] f<
--   | TS.inj₂ notinl' with whrDet* (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA) ) ((red A⇒A'') , αₙ αA')
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (ϝᵣ mε A⇒A'' αA' tA fA)) [B'] f<
--   | TS.inj₂ notinl' | PE.refl with αNeutralHProp (αNeNotIn notinl' αA) αA'
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (ϝᵣ mε A⇒A'' αA' tA fA)) [B'] f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (emb 0<1 (ϝᵣ mε A⇒A'' αA' tA fA)) [B'] f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl | PE.refl =
--    emb⁰¹ (ϝᵣ-l A⇒A'' αA' [B'] tA fA (τTyLog [B']) (τTyLog [B'])
--                (ShapeView≤ tAB tA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
--                (ShapeView≤ fAB fA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _))))
-- -- Special case of diagonal left αNeutrals
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
--   | TS.inj₂ notinl' 
--   with whrDet* (red (wfRed≤* f< A⇒A') , αₙ (αNeNotIn notinl' αA) ) ((red A⇒A'') , αₙ αA')
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
--   | TS.inj₂ notinl'  | PE.refl with αNeutralHProp (αNeNotIn notinl' αA) αA'
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
-- ShapeView≤ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ϝᵣ mε A⇒A'' αA' tA fA) [B'] f<
--   | TS.inj₂ notinl'  | PE.refl | PE.refl | PE.refl =
--     ϝᵣ-l A⇒A'' αA' [B'] tA fA (τTyLog [B']) (τTyLog [B'])
--       (ShapeView≤ tAB tA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
--       (ShapeView≤ fAB fA (τTyLog [B']) (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))

-- -- Right αNeutrals with embedding
-- ShapeView≤ {l' = l'} (ϝᵣ-r {n = n} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   with decidInLConNat l' n
-- ShapeView≤ {l' = l'} (ϝᵣ-r {n = n} {nε = nε} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   | TS.inj₁ (TS.inj₁ nε') =
--     ShapeView≤ tAB [A'] [B'] (≤ₗ-add _ _ _ f< nε')
-- ShapeView≤ {l' = l'}  (ϝᵣ-r {n = n} B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] [B'] f<
--   | TS.inj₁ (TS.inj₂ nε') =
--     ShapeView≤ fAB [A'] [B'] (≤ₗ-add _ _ _ f< nε')
-- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (ℕᵣ ℕB)) f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
--            (whrDet* (red ℕB , ℕₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (𝔹ᵣ 𝔹B)) f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (𝔹≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
--            (whrDet* (red 𝔹B , 𝔹ₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- -- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (Emptyᵣ D)) f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
-- --                     (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- -- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (Unitᵣ D)) f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
-- --                     (whrDet* (red D , Unitₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A']
--            (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext))  f<
--   | TS.inj₂ notinl' =
--   ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αB)
--                     (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A']
--            (emb 0<1 (ne′ K D₁ neK K≡K))  f<
--   | TS.inj₂ notinl' =
--     ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αB) (whrDet* (red D₁ , ne neK)
--                    (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (ϝᵣ mε B⇒B'' αB' tB fB)) f<
--   | TS.inj₂ notinl' with whrDet* (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB) ) ((red B⇒B'') , αₙ αB')
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (ϝᵣ mε B⇒B'' αB' tB fB)) f<
--   | TS.inj₂ notinl' | PE.refl with αNeutralHProp (αNeNotIn notinl' αB) αB'
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (emb 0<1 (ϝᵣ mε B⇒B'' αB' tB fB)) f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A']
--            (emb 0<1 (ϝᵣ mε B⇒B'' αB' tB fB)) f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl | PE.refl =
--    emb¹⁰ (ϝᵣ-r B⇒B'' αB' [A'] (τTyLog [A']) (τTyLog [A']) tB fB
--               (ShapeView≤ tAB (τTyLog [A']) tB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
--               (ShapeView≤ fAB (τTyLog [A']) fB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _))))

-- -- Right αNeutrals
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Uᵣ UB) f<
--   | TS.inj₂ notinl' = ⊥-elim (U≢αne αB (whnfRed* (red B⇒B') Uₙ))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ℕᵣ ℕB) f<
--   | TS.inj₂ notinl' =
--     ⊥-elim (ℕ≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
--                   (whrDet* (red ℕB , ℕₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (𝔹ᵣ 𝔹B) f<
--   | TS.inj₂ notinl' =
--     ⊥-elim (𝔹≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
--                   (whrDet* (red 𝔹B , 𝔹ₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- -- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Emptyᵣ D) f<
-- --   | TS.inj₂ notinl' = 
-- --   ⊥-elim (Empty≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
-- --                     (whrDet* (red D , Emptyₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- -- ShapeView≤ {lε' = lε'}  (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (Unitᵣ D) f<
-- --   | TS.inj₂ notinl' =
-- --   ⊥-elim (Unit≢αne {_} {_} {_} {lε'} (αNeNotIn notinl' αB)
-- --                     (whrDet* (red D , Unitₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'}  (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A']
--            (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) f<
--   | TS.inj₂ notinl' = 
--   ⊥-elim (B≢αne {_} {_} {_} {_} {_} {lε'} W (αNeNotIn notinl' αB)
--                     (whrDet* (red D , ⟦ W ⟧ₙ) (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ {lε' = lε'} (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ne′ K D₁ neK K≡K) f<
--   | TS.inj₂ notinl' =
--     ⊥-elim (ne≢αne {_} {_} {_} {_} {_} {lε'} neK (αNeNotIn notinl' αB) (whrDet* (red D₁ , ne neK)
--                    (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB))))
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
--   | TS.inj₂ notinl'
--   with whrDet* (red (wfRed≤* f< B⇒B') , αₙ (αNeNotIn notinl' αB) ) ((red B⇒B'') , αₙ αB')
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
--   | TS.inj₂ notinl' | PE.refl with αNeutralHProp (αNeNotIn notinl' αB) αB'
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
--   | TS.inj₂ notinl' | PE.refl | PE.refl with NotInLConNatHProp _ _ mε notinl'
-- ShapeView≤ (ϝᵣ-r B⇒B' αB [B] [A]t [A]f [B]t [B]f tAB fAB) [A'] (ϝᵣ mε B⇒B'' αB' tB fB) f<
--   | TS.inj₂ notinl'  | PE.refl | PE.refl | PE.refl =
--     ϝᵣ-r B⇒B'' αB' [A'] (τTyLog [A']) (τTyLog [A']) tB fB
--       (ShapeView≤ tAB (τTyLog [A']) tB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))
--       (ShapeView≤ fAB (τTyLog [A']) fB (≤ₗ-add _ _ _ (λ n b ne₁ → InThere _ (f< n b ne₁) _ _) (InHereNat _)))

-- τShapeView : ∀ {k k′} {l : LCon} {lε : ⊢ₗ l} {n b nε}
--                       {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
--                       ([AB] : ShapeView Γ k k′ A B [A] [B])
--                       → ShapeView Γ k k′ A B (τTyLog {n = n} {b = b} {nε = nε} [A]) (τTyLog [B])
-- τShapeView [AB] = ShapeView≤ [AB] _ _ (λ m b' mε → InThere _ mε _ _)

-- Construct an shape view from an equality (aptly named)
goodCases : ∀ {k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
            (A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]) → ShapeView Γ k k′ A B [A] [B] A≡B
-- Diagonal cases
goodCases (Uᵣ UA) (Uᵣ UB) (⊩¹≡U _ U≡B) = Uᵥ UA UB U≡B
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) (⊩¹≡ℕ _ A⇒N) = ℕᵥ ℕA ℕB A⇒N
goodCases (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (⊩¹≡𝔹 _ A⇒N) = 𝔹ᵥ 𝔹A 𝔹B A⇒N
goodCases (ne neA) (ne neB) (⊩¹≡ne _ A=B) = ne neA neB A=B
goodCases (Bᵣ BΣ ΣA) (Bᵣ BΣ ΣB) (⊩¹≡B BΣ _ A≡B) = Bᵥ BΣ ΣA ΣB A≡B
goodCases (Bᵣ BΠ ΠA) (Bᵣ BΠ ΠB) (⊩¹≡B BΠ _ A≡B) = Bᵥ BΠ ΠA ΠB A≡B
-- goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
-- goodCases (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B = Unitᵥ UnitA UnitB

goodCases {k = k} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {k = k} {⁰} [A] x A≡B)
goodCases {k′ = k} (emb 0<1 x) [B] (⊩¹≡emb _ [A] A≡B) =
  emb⁰¹ (goodCases [A] [B] A≡B)


-- Left αNeutrals

goodCases [A] [B] (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B fA≡B) =
  ϝᵣ-l A⇒A' αA' [B] tA fA (τTyLog [B]) (τTyLog [B]) tA≡B fA≡B (goodCases tA _ tA≡B) (goodCases fA _ fA≡B)

-- Right αNeutrals

goodCases [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
  with whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)
goodCases [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
 | PE.refl with αNeutralHProp αB' αB
goodCases [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
 | PE.refl | PE.refl with NotInLConNatHProp _ _ mε' mε
goodCases [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
 | PE.refl | PE.refl | PE.refl =
   ϝᵣ-r A⇒B A⇒B' αB αB' [A] tA fA [A]t [A]f tA≡B fA≡B
        (goodCases tA [A]t tA≡B) (goodCases fA [A]f fA≡B)

-- Refutable cases
-- U ≡ _
goodCases (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) (⊩¹≡U _ PE.refl) with whnfRed* (red D) Uₙ
... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (𝔹ᵣ D) (⊩¹≡U _ PE.refl) with whnfRed* (red D) Uₙ
... | ()
-- goodCases (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- ... | ()
-- goodCases (Uᵣ′ _ _ ⊢Γ) (Unitᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- ... | ()
goodCases (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) (⊩¹≡U _ PE.refl) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡U _ PE.refl) =
  ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ ⊢Γ) (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡U _ PE.refl) =
  ⊥-elim (U≢αne αB (whnfRed* (red A⇒B) Uₙ))

-- Refutable right αNeutrals
goodCases [A] (Uᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) =
  ⊥-elim (U≢αne αB' (whnfRed* (red B⇒B') Uₙ))
goodCases [A] (ℕᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) =
  ⊥-elim (ℕ≢αne αB' (whrDet* (red D , ℕₙ) (red B⇒B' , αₙ αB')))
goodCases [A] (𝔹ᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) =
  ⊥-elim (𝔹≢αne αB' (whrDet* (red D , 𝔹ₙ) (red B⇒B' , αₙ αB')))
-- goodCases [A] (Emptyᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) =
--   ⊥-elim (Empty≢αne αB' (whrDet* (red D , Emptyₙ) (red B⇒B' , αₙ αB')))
-- goodCases [A] (Unitᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) =
--   ⊥-elim (Unit≢αne αB' (whrDet* (red D , Unitₙ) (red B⇒B' , αₙ αB')))
goodCases [A] (ne′ K D neK K≡K) (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) =
  ⊥-elim (ne≢αne neK αB' (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB')))
goodCases [A] (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) =
    ⊥-elim (B≢αne BΠ αB' (whrDet* (red D , Πₙ) (red B⇒B' , αₙ αB')))
goodCases [A] (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) =
    ⊥-elim (B≢αne BΣ αB' (whrDet* (red D , Σₙ) (red B⇒B' , αₙ αB')))

-- ℕ ≡ _
goodCases {k = k} {k′ = k′} (ℕᵣ D) (Uᵣ ⊢Γ) ℕ≡U = ⊥-elim (ℕ≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ ℕ≡U)
goodCases (ℕᵣ D) (𝔹ᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , 𝔹ₙ)
... | ()
-- goodCases (ℕᵣ D) (Emptyᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , Emptyₙ) (red D' , 𝔹ₙ)
-- ... | ()
-- goodCases (ℕᵣ D) (Unitᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Unitₙ)
-- ... | ()
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) (⊩¹≡ℕ _ A⇒N) =
  ⊥-elim (ℕ≢ne neK (whrDet* (A⇒N , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡ℕ _ A⇒N) =
  ⊥-elim (ℕ≢B W (whrDet* (A⇒N , ℕₙ) (red D₁ , ⟦ W ⟧ₙ)))
goodCases (ℕᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ℕ _ A⇒N) = ⊥-elim (ℕ≢αne αB (whrDet* (A⇒N , ℕₙ) (red A⇒B , αₙ αB)))

-- -- 𝔹 ≡ _
-- goodCases (𝔹ᵣ 𝔹A) [B] A≡B = goodCases𝔹 𝔹A [B] A≡B
goodCases {k = k} {k′ = k′} (𝔹ᵣ D) (Uᵣ ⊢Γ) 𝔹≡U = ⊥-elim (𝔹≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ 𝔹≡U)
goodCases (𝔹ᵣ D) (ℕᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , ℕₙ)
... | ()
-- goodCases (𝔹ᵣ D) (ℕᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , ℕₙ)
-- ... | ()
-- goodCases (𝔹ᵣ D) (Unitᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , Unitₙ)
-- ... | ()
goodCases (𝔹ᵣ D) (ne′ K D₁ neK K≡K) (⊩¹≡𝔹 _ A⇒N) =
  ⊥-elim (𝔹≢ne neK (whrDet* (A⇒N , 𝔹ₙ) (red D₁ , ne neK)))
goodCases (𝔹ᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡𝔹 _ A⇒N) =
  ⊥-elim (𝔹≢B W (whrDet* (A⇒N , 𝔹ₙ) (red D₁ , ⟦ W ⟧ₙ)))
goodCases (𝔹ᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡𝔹 _ A⇒N) = ⊥-elim (𝔹≢αne αB (whrDet* (A⇒N , 𝔹ₙ) (red A⇒B , αₙ αB)))


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

-- ne ≡ _
-- goodCases (ne neA) [B] A≡B = goodCasesNe neA [B] A≡B
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (𝔹ᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
  ⊥-elim (𝔹≢ne neM (whrDet* (red D₁ , 𝔹ₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
--   ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
-- goodCases (ne′ K D neK K≡K) (Unitᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
--  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
  ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (ϝᵣ mε A⇒B αB [A]t [A]f)  (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) =
  ⊥-elim (ne≢αne neM αB (whrDet* (red D′ , ne neM) (red A⇒B , αₙ αB)))

-- Π ≡ _
-- goodCases (Bᵣ W BA) ⊢B A≡B = goodCasesW W BA ⊢B A≡B


goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whnfRed* D′ Uₙ
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whnfRed* D′ Uₙ
... | ()
goodCases (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) =
          ⊥-elim (ℕ≢B W (whrDet* (red D₁ , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
goodCases (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (𝔹ᵣ D₁)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) =
          ⊥-elim (𝔹≢B W (whrDet* (red D₁ , 𝔹ₙ) (D′ , ⟦ W ⟧ₙ)))
-- goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
--           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
-- ... | ()
-- goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
--           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
-- ... | ()
goodCases (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΠ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (⊩¹≡B _ _ (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′])) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
... | ()
goodCases (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
  (⊩¹≡B _ _ (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′])) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
... | ()
goodCases (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) =
  ⊥-elim (B≢ne W neK (whrDet* (D′ ,  ⟦ W ⟧ₙ) (red D₁ , ne neK)))
goodCases (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [A]t [A]f)
          (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) =
          ⊥-elim (B≢αne W αB (whrDet* (D′ ,  ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))



-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {k k′ A} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([A′] : Γ / lε ⊩⟨ k′ ⟩ A)
              → ShapeView Γ k k′ A A [A] [A′] (reflEq [A])
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])





-- A view for constructor equality between three types
data ShapeView₃ (Γ : Con Term n) : ∀ {l : LCon} {lε : ⊢ₗ l} k k′ k″ A B C
                 (p : Γ / lε ⊩⟨ k   ⟩ A)
                 (q : Γ / lε ⊩⟨ k′  ⟩ B)
                 (r : Γ / lε ⊩⟨ k″ ⟩ C)
                 (A≡B :  Γ / lε ⊩⟨ k ⟩ A ≡ B / p)
                 (B≡C :  Γ / lε ⊩⟨ k′ ⟩ B ≡ C / q) → Set where
  Uᵥ : ∀ {l lε k k′ k″} UA UB UC U≡B U≡C
     → ShapeView₃ Γ {l} {lε} k k′ k″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC) (⊩¹≡U UA U≡B) (⊩¹≡U UB U≡C)
  ℕᵥ : ∀ {A B C k k′ k″} ℕA ℕB ℕC ℕ≡B ℕ≡C
    → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC) (⊩¹≡ℕ ℕA ℕ≡B) (⊩¹≡ℕ ℕB ℕ≡C)
  𝔹ᵥ : ∀ {A B C k k′ k″} 𝔹A 𝔹B 𝔹C 𝔹≡B 𝔹≡C
    → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (𝔹ᵣ 𝔹C) (⊩¹≡𝔹 𝔹A 𝔹≡B) (⊩¹≡𝔹 𝔹B 𝔹≡C)
--   Emptyᵥ : ∀ {l} {lε}  {A B C k k′ k″} EmptyA EmptyB EmptyC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
--   Unitᵥ : ∀ {l} {lε}  {A B C k k′ k″} UnitA UnitB UnitC
--     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
  ne  : ∀ {l} {lε}  {A B C k k′ k″} neA neB neC neA≡B neB≡C
      → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ne neA) (ne neB) (ne neC) (⊩¹≡ne neA neA≡B) (⊩¹≡ne neB neB≡C)
  Bᵥ : ∀ {l} {lε}  {A B C k k′ k″} W BA BB BC BA≡B BB≡C
    → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W BC) (⊩¹≡B W BA BA≡B) (⊩¹≡B W BB BB≡C)
  ϝᵣ-l : ∀ {l lε n nε} {k k' k'' A A' B C} (A⇒A' : Γ / lε ⊢ A :⇒*: A') αA [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f
           B≡C tA≡B fA≡B tB≡C fB≡C 
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C [A]t [B]t [C]t tA≡B tB≡C
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C [A]f [B]f [C]f fA≡B fB≡C
         → ShapeView₃ Γ {l} {lε}                  k k' k'' A  B C (ϝᵣ nε A⇒A' αA [A]t [A]f) [B] [C]
                                                                      (⊩¹≡ϝ-l A⇒A' αA [A]t [A]f tA≡B fA≡B) B≡C
  ϝᵣ-m : ∀ {l lε n nε} {k k' k'' A B B' C} (B⇒B' : Γ / lε ⊢ B :⇒*: B') αB [A] [C] [A]t [A]f [B]t [B]f [C]t [C]f
           A≡B tA≡B fA≡B tB≡C fB≡C
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C [A]t [B]t [C]t tA≡B tB≡C
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C [A]f [B]f [C]f fA≡B fB≡C
         → ShapeView₃ Γ {l} {lε}                  k k' k'' A B  C [A] (ϝᵣ nε B⇒B' αB [B]t [B]f) [C] A≡B
                                                                      (⊩¹≡ϝ-l B⇒B' αB [B]t [B]f tB≡C fB≡C)
  ϝᵣ-r : ∀ {l lε n nε} {k k' k'' A B C C'} (C⇒C' : Γ / lε ⊢ C :⇒*: C') αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f
           A≡B tA≡B fA≡B tB≡C fB≡C
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C [A]t [B]t [C]t tA≡B tB≡C
         → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C [A]f [B]f [C]f fA≡B fB≡C
         → ShapeView₃ Γ {l} {lε}                  k k' k'' A B C  [A]  [B] (ϝᵣ nε C⇒C' αC [C]t [C]f) A≡B
                                                                      (⊩¹≡ϝ-r C⇒C' αC [B] [B]t [B]f tB≡C fB≡C)
  emb⁰¹¹ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
         → ShapeView₃ Γ {l} {lε}  ⁰ k k′ A B C p q r A≡B B≡C
         → ShapeView₃ Γ {l} {lε}  ¹ k k′ A B C (emb 0<1 p) q r (⊩¹≡emb 0<1 p A≡B) B≡C
  emb¹⁰¹ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
         → ShapeView₃ Γ {l} {lε}  k ⁰ k′ A B C p q r A≡B B≡C
         → ShapeView₃ Γ {l} {lε}  k ¹ k′ A B C p (emb 0<1 q) r A≡B (⊩¹≡emb 0<1 q B≡C)
  emb¹¹⁰ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
         → ShapeView₃ Γ {l} {lε}  k k′ ⁰ A B C p q r A≡B B≡C
         → ShapeView₃ Γ {l} {lε}  k k′ ¹ A B C p q (emb 0<1 r) A≡B B≡C


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
-- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (𝔹ᵥ 𝔹A 𝔹B) =
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹A , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
-- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
-- --   ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
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
-- combineU (Uᵥ UA UB) (𝔹ᵥ 𝔹A 𝔹B) with whnfRed* (red 𝔹A) Uₙ
-- ... | ()
-- -- combineU (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
-- -- ... | ()
-- -- combineU (Uᵥ UA UB) (Unitᵥ UnA UnB) with whnfRed* (red UnA) Uₙ
-- -- ... | ()
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
-- combineℕ (ℕᵥ ℕA ℕB) (𝔹ᵥ 𝔹A 𝔹B) with whrDet* (red ℕB , ℕₙ) (red 𝔹A , 𝔹ₙ)
-- ... | ()
-- -- combineℕ (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
-- -- ... | ()
-- -- combineℕ (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
-- -- ... | ()
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

-- combine𝔹 : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C 𝔹A 𝔹B [B]′ [C]}
--           → ShapeView Γ {l} {lε} k k′ A B (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B)
--           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
--           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) [C]
-- combine𝔹 (𝔹ᵥ 𝔹A₁ 𝔹B₁) (𝔹ᵥ 𝔹A 𝔹B) = 𝔹ᵥ 𝔹A₁ 𝔹B₁ 𝔹B
-- combine𝔹 [AB] (emb⁰¹ [BC]) = combine𝔹 [AB] [BC]
-- combine𝔹 [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine𝔹 [AB] [BC])
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Uᵥ UA UB) with whnfRed* (red 𝔹B) Uₙ
-- ... | ()
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ℕᵥ ℕA ℕB) with whrDet* (red 𝔹B , 𝔹ₙ) (red ℕA , ℕₙ)
-- ... | ()
-- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Emptyᵥ EmptyA EmptyB) with whrDet* (red 𝔹B , 𝔹ₙ) (red EmptyA , Emptyₙ)
-- -- ... | ()
-- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Unitᵥ UnA UnB) with whrDet* (red 𝔹B , 𝔹ₙ) (red UnA , Unitₙ)
-- -- ... | ()
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ne (ne K D neK K≡K) neB) =
--   ⊥-elim (𝔹≢ne neK (whrDet* (red 𝔹B , 𝔹ₙ) (red D , ne neK)))
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
--   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹B , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
--   ⊥-elim (𝔹≢αne αA (whrDet* (red 𝔹B , 𝔹ₙ) (red A⇒A' , αₙ αA)))
-- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
--   ϝᵣ-r C⇒C' αC (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (𝔹ᵣ (τwfRed* 𝔹A)) (𝔹ᵣ (τwfRed* 𝔹A))
--     (𝔹ᵣ (τwfRed* 𝔹B)) (𝔹ᵣ (τwfRed* 𝔹B)) [C]t [C]f
--     (combine𝔹 (𝔹ᵥ (τwfRed* 𝔹A) (τwfRed* 𝔹B)) tBC)
--     (combine𝔹 (𝔹ᵥ (τwfRed* 𝔹A) (τwfRed* 𝔹B)) fBC)


-- -- combineUnit : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C UnitA UnitB [B]′ [C]}
-- --           → ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
-- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) [C]
-- -- combineUnit (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
-- -- combineUnit [AB] (emb⁰¹ [BC]) = combineUnit [AB] [BC]
-- -- combineUnit [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineUnit [AB] [BC])
-- -- combineUnit (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
-- -- ... | ()
-- -- combineUnit (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
-- -- ... | ()
-- -- combineUnit (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
-- -- ... | ()
-- -- combineUnit (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
-- --   ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
-- -- combineUnit (Unitᵥ UnitA UnitB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- --   ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- -- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- --   ⊥-elim (Unit≢αne αA (whrDet* (red UnitB , Unitₙ) (red A⇒A' , αₙ αA)))
-- -- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- --   ϝᵣ-r C⇒C' αC (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ (τwfRed* UnitA)) (Unitᵣ (τwfRed* UnitA))
-- --     (Unitᵣ (τwfRed* UnitB)) (Unitᵣ (τwfRed* UnitB)) [C]t [C]f
-- --     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) tBC)
-- --     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) fBC)


-- -- combineE : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C EA EB [B]′ [C]}
-- --           → ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EA) (Emptyᵣ EB)
-- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Emptyᵣ EA) (Emptyᵣ EB) [C]
-- -- combineE (Emptyᵥ EA₁ EB₁) (Emptyᵥ EA EB) = Emptyᵥ EA₁ EB₁ EB
-- -- combineE [AB] (emb⁰¹ [BC]) = combineE [AB] [BC]
-- -- combineE [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineE [AB] [BC])
-- -- combineE (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
-- -- ... | ()
-- -- combineE (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
-- -- ... | ()
-- -- combineE (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
-- -- ... | ()
-- -- combineE (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
-- --   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
-- -- combineE (Emptyᵥ EmptyA EmptyB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- combineE (Emptyᵥ EmptyA EmptyB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- --   ⊥-elim (Empty≢αne αA (whrDet* (red EmptyB , Emptyₙ) (red A⇒A' , αₙ αA)))
-- -- combineE (Emptyᵥ EA EB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- --   ϝᵣ-r C⇒C' αC (Emptyᵣ EA) (Emptyᵣ EB) (Emptyᵣ (τwfRed* EA)) (Emptyᵣ (τwfRed* EA))
-- --     (Emptyᵣ (τwfRed* EB)) (Emptyᵣ (τwfRed* EB)) [C]t [C]f
-- --     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) tBC)
-- --     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) fBC)


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
-- combineNe (ne neA (ne K D neK K≡K)) (𝔹ᵥ 𝔹A 𝔹B) =
--   ⊥-elim (𝔹≢ne neK (whrDet* (red 𝔹A , 𝔹ₙ) (red D , ne neK)))
-- -- combineNe (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
-- --   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
-- -- combineNe (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
-- --   ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
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


  
  -- Combines two two-way views into a three-way view

-- combine : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C [A] [B] [B]′ [C] A≡B B≡C}
--         → ShapeView Γ {l} {lε} k k′ A B [A] [B] A≡B 
--         → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C] B≡C
--         → ShapeView₃ Γ {l} {lε} k k″ k‴ A B C [A] [B]′ [C] A≡B B≡C
-- -- Diagonal cases
-- combine (emb⁰¹ [AB]) [BC] = {!!} -- emb⁰¹¹ (combine [AB] [BC])
-- combine (emb¹⁰ [AB]) [BC] = {!!} -- emb¹⁰¹ (combine [AB] [BC])
-- combine [AB] (emb⁰¹ [BC]) = {!!} -- combine [AB] [BC]
-- combine [AB] (emb¹⁰ [BC]) = {!!} -- emb¹¹⁰ (combine [AB] [BC])
                                                 
-- -- Π/Σ ≡ _
-- combine (Bᵥ W BA BB BA≡B) [BC] = {!!} --combineW-l W (Bᵥ W BA BB) [BC]

                                                      
-- -- U ≡ _
-- combine (Uᵥ UA UB UA≡B) [BC] = {!!} -- combineU (Uᵥ UA UB) [BC]

-- -- ℕ ≡ _
-- combine (ℕᵥ ℕA ℕB ℕA≡B) [BC] = {!!} -- combineℕ (ℕᵥ ℕA ℕB) [BC]

-- -- 𝔹 ≡ _
-- combine (𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B) [BC] = {!!} -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) [BC]

-- -- -- Empty ≡ _
-- -- combine (Emptyᵥ EmptyA EmptyB) = combineE (Emptyᵥ EmptyA EmptyB) 

-- -- -- Unit ≡ _
-- -- combine (Unitᵥ UnitA UnitB) = combineUnit (Unitᵥ UnitA UnitB)

-- -- ne ≡ _
-- combine (ne neA neB neA≡B) = {!!} -- combineNe (ne neA neB)
                                         
-- -- combine (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne neB (ne K D neK K≡K)) = {!!}
-- combine {[C] = [C]} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) [BC] = {!!}
-- --  ϝᵣ-l A⇒A' αA [B] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
-- --       (combine tAB (ShapeView≤ [BC] [B]t (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
-- --       (combine fAB (ShapeView≤ [BC] [B]f (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
                                                                                 
-- combine {[B]′ = [B]′} {[C] = [C]} (ϝᵣ-r B⇒B' B⇒B'' αB αB' [A] [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) [BC] = {!!}
-- --  ϝᵣ-m B⇒B' αB [A] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
-- --  (combine tAB (ShapeView≤ [BC] (τTyLog [B]′) (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
-- --  (combine fAB (ShapeView≤ [BC] (τTyLog [B]′) (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
                                                                                


-- -- TyLogℕ : ∀ {l : LCon} {lε : ⊢ₗ l} {k}
-- --            → (ℕA : Γ / lε ⊩ℕ A)
-- --            → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
-- --            → ∃ (λ K → [A] PE.≡ ℕ-intr K) -- TS.⊎ ∃₂ (λ k' (k< : k' < k) → ∃ (λ K → [A] PE.≡ emb k< (ℕᵣ K)))
-- -- TyLogℕ {k = k} ℕA [A] with goodCasesRefl {k = k} (ℕᵣ ℕA) [A]
-- -- TyLogℕ ℕA [A] | ℕᵥ ℕA ℕA' = noemb ℕA' , PE.refl
-- -- TyLogℕ ℕA (emb 0<1 [A]) | emb¹⁰ [AB] with TyLogℕ ℕA [A]
-- -- TyLogℕ ℕA (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- TyLogℕ ℕA [A] | ϝᵣ-r B⇒B' αB (ℕᵣ ℕA) [A]t [A]f [B]t [B]f tAB fAB = ⊥-elim (ℕ≢αne αB (whrDet* (red ℕA , ℕₙ) (red B⇒B' , αₙ αB)))

-- -- TyLog𝔹 : ∀ {l : LCon} {lε : ⊢ₗ l} {k}
-- --            → (𝔹A : Γ / lε ⊩𝔹 A)
-- --            → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
-- --            → ∃ (λ K → [A] PE.≡ 𝔹-intr K) -- TS.⊎ ∃₂ (λ k' (k< : k' < k) → ∃ (λ K → [A] PE.≡ emb k< (𝔹ᵣ K)))
-- -- TyLog𝔹 {k = k} 𝔹A [A] with goodCasesRefl {k = k} (𝔹ᵣ 𝔹A) [A]
-- -- TyLog𝔹 𝔹A [A] | 𝔹ᵥ 𝔹A 𝔹A' = noemb 𝔹A' , PE.refl
-- -- TyLog𝔹 𝔹A (emb 0<1 [A]) | emb¹⁰ [AB] with TyLog𝔹 𝔹A [A]
-- -- TyLog𝔹 𝔹A (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- TyLog𝔹 𝔹A [A] | ϝᵣ-r B⇒B' αB (𝔹ᵣ 𝔹A) [A]t [A]f [B]t [B]f tAB fAB = ⊥-elim (𝔹≢αne αB (whrDet* (red 𝔹A , 𝔹ₙ) (red B⇒B' , αₙ αB)))


-- -- TyLogW : ∀ {l : LCon} {lε : ⊢ₗ l} {k k'} W
-- --            → (WA : Γ / lε ⊩′⟨ k ⟩B⟨ W ⟩ A)
-- --            → ([A] :  Γ / lε ⊩⟨ k' ⟩ A)
-- --            → ∃ (λ K → [A] PE.≡ B-intr W K)
-- -- TyLogW {k = k} W WA [A] with goodCasesRefl {k = k} (Bᵣ W WA) [A]
-- -- TyLogW W WA [A] | Bᵥ W BA BA' = noemb BA' , PE.refl
-- -- TyLogW W WA (emb 0<1 [A]) | emb¹⁰ [AB] with TyLogW W WA [A]
-- -- TyLogW W WA (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- TyLogW W WA [A] | ϝᵣ-r B⇒B' αB (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB =
-- --   ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (red B⇒B' , αₙ αB)))



-- -- -- LogW0 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
-- -- --        ([A] : Γ / lε' ⊩⟨ ⁰ ⟩ A) (f< : l ≤ₗ l')
-- -- --        → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA'))
-- -- -- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = (BA' , PE.refl)
-- -- -- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = (BA' , PE.refl)
-- -- -- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- --   with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
-- -- -- ... | ()
-- -- -- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- --   with (whrDet* ( red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
-- -- -- ... | ()
-- -- -- LogW0 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
-- -- --   ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
-- -- --   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
-- -- --   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
-- -- --   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
-- -- --   ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb () [A]) 
-- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
-- -- --   ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))


-- -- -- LogW1 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
-- -- --        ([A] : Γ / lε' ⊩⟨ ¹ ⟩ A) (f< : l ≤ₗ l')
-- -- --        → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA')) TS.⊎ (∃ (λ BA' → [A] PE.≡ emb 0<1 (Bᵣ W BA')))
-- -- -- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = TS.inj₁ (BA' , PE.refl)
-- -- -- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = TS.inj₁ (BA' , PE.refl)
-- -- -- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- --   with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
-- -- -- ... | ()
-- -- -- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- --   with (whrDet* (red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
-- -- -- ... | ()
-- -- -- LogW1 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
-- -- --   ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
-- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
-- -- --   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
-- -- --   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
-- -- --   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
-- -- --   ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- -- -- LogW1 W BA (emb 0<1 [A]) f< with LogW0 W BA [A] f<
-- -- -- LogW1 W BA (emb 0<1 [A]) f< | BA' , PE.refl = TS.inj₂ (BA' , PE.refl)
-- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
-- -- --   ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))
