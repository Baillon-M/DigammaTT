{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
import Definition.Typed.Weakening as Wk
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Γ′ : Con Term n
    l : LCon
    lε : ⊢ₗ l



-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ k}
             → A PE.≡ A′
             → Γ / lε ⊩⟨ k ⟩ A
             → Γ / lε ⊩⟨ k ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {k A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  / lε ⊩⟨ k ⟩ A
              → Γ′ / lε ⊩⟨ k ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B k k′} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B k k′} (eq : A PE.≡ A′)
                   (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                 → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ k k′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                  → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ k} (eqB : B PE.≡ B′) (p : Γ / lε ⊩⟨ k ⟩ A)
                  → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types and
  -- a lifting of propositionally equal types
  irrelevanceEqLift″ : ∀ {A A′ B B′ C C′ k k′}
                        (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
                        (p : Γ ∙ C / lε ⊩⟨ k ⟩ A) (q : Γ ∙ C′ / lε ⊩⟨ k′ ⟩ A′)
                      → Γ ∙ C / lε ⊩⟨ k ⟩ A ≡ B / p → Γ ∙ C′ / lε ⊩⟨ k′ ⟩ A′ ≡ B′ / q
  irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A}
                       → ShapeView Γ k k′ A A p q
                       → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (𝔹ᵥ D D′) A≡B = A≡B
--   irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
--  irrelevanceEqT (Unitᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ _ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
    ne₌ _ M D′ neM K≡M
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) = {!!}
  irrelevanceEqT {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity W ΠFG≡ΠF₁G₁
    in  B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ (PE.subst (λ x → Γ / lε ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {m} {ρ} {Δ} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ →
              irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                                    ([F]₁ [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
           (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (Bϝ _ B⇒B' αB [A]t [A]f tA≡B fA≡B) = Bϝ _ B⇒B' αB {!!} {!!} (irrelevanceEqT {!!} tA≡B) {!!}
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl = irrelevanceEqT {!!} tA≡B , {!!}
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B =
    PE.⊥-elim (U≢αne αB (whnfRed* (red B⇒B') Uₙ))
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (emb 0<1 [B]) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
  irrelevanceEqT (ϝᵣ-r B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t k k′} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A)
                  → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t k k′} (eq : A PE.≡ A′)
                     (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                   → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ k k′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                    → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {k k′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  / lε ⊩⟨ k  ⟩ A)
                       ([A′] : Γ′ / lε ⊩⟨ k′ ⟩ A′)
                     → Γ  / lε ⊩⟨ k  ⟩ t ∷ A  / [A]
                     → Γ′ / lε ⊩⟨ k′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {A t k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A}
                         → ShapeView Γ k k′ A A p q
                         → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (𝔹ᵥ D D′) t = t
--   irrelevanceTermT (Emptyᵥ D D′) t = t
--   irrelevanceTermT (Unitᵥ D D′) t = t
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
    in  Πₜ f (PE.subst (λ x → Γ / lε ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → Γ / lε ⊢ f ≅ f ∷ x) ΠFG≡ΠF₁G₁ f≡f)
           (λ {_} {ρ} {Δ} {a} {b} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁ →
              let [a]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                           ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
                  [b]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                           ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [b]₁
                  [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                             ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a≡b]₁
              in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                     ([f] [ρ] ⊢Δ [a] [b] [a≡b]))
          (λ {_} {ρ} {_} {b} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                  ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f]₁ [ρ] ⊢Δ [a]))
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Σₜ p d pProd p≅p [fst] [snd]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        [fst]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fst]
        [snd]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
          ([G] Wk.id (wf ⊢F) [fst]) ([G]₁ Wk.id (wf ⊢F₁) [fst]′)
          [snd]
    in  Σₜ p (PE.subst (λ x → Γ / lε ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d) pProd
           (PE.subst (λ x → Γ / lε ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p)
           [fst]′ [snd]′
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u k k′} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A)
                    → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u k k′} (eq : A PE.≡ A′)
                       (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                     → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ k k′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
                      → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A}
                           → ShapeView Γ k k′ A A p q
                           → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (𝔹ᵥ D D′) t≡u = t≡u
--   irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
--   irrelevanceEqTermT (Unitᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
        [A]         = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ f g (PE.subst (λ x → Γ / lε ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d)
            (PE.subst (λ x → Γ / lε ⊢ u :⇒*: g ∷ x) ΠFG≡ΠF₁G₁ d′) funcF funcG
            (PE.subst (λ x → Γ / lε ⊢ f ≅ g ∷ x) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                          ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a]))
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        [A]         = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {_} {_} {≤ε}) [G] G-ext
        [A]₁        = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ (λ {m} {l'} {≤ε} → [F]₁ {_} {_} {≤ε}) [G]₁ G-ext₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk Wk.id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
          ([G] Wk.id (wf ⊢F) [fstp]) ([G]₁ Wk.id (wf ⊢F₁) [fstp]′)
          [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ / lε ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ / lε ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ / lε ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            [fstp]′
            [fstr]′
            [fst≡]′
            [snd≡]′
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
