{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
import Definition.Typed.Weakening as Wk
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.ShapeView

open import Tools.Nat
open import Tools.Product
import Tools.Sum as TS
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
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceTermT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl = irrelevanceTermT (goodCasesRefl [A]t tB) tA≡B , irrelevanceTermT (goodCasesRefl [A]f fB) fA≡B
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceTermT (ϝᵣ-l {nε = nε} A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl = irrelevanceTermT (goodCasesRefl [A]t tB) tA≡B , irrelevanceTermT (goodCasesRefl [A]f fB) fA≡B
  irrelevanceTermT (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) t = {!!}

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
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqTermT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl = irrelevanceEqTermT (goodCasesRefl [A]t tB) tA≡B , irrelevanceEqTermT (goodCasesRefl [A]f fB) fA≡B
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqTermT (ϝᵣ-l {nε = nε} A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl = irrelevanceEqTermT (goodCasesRefl [A]t tB) tA≡B , irrelevanceEqTermT (goodCasesRefl [A]f fB) fA≡B
  irrelevanceEqTermT (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) t≡u = {!!}

  -- Irrelevance for type equality with propositionally equal second types
irrelevanceEqR′ : ∀ {A B B′ k} (eqB : B PE.≡ B′) (p : Γ / lε ⊩⟨ k ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k ⟩ A ≡ B′ / p
irrelevanceEqR′ PE.refl p A≡B = A≡B

mutual
  convTermT₁ : ∀ {k k′ A B t} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
             → ShapeView Γ k k′ A B [A] [B]
             → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
             → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
             → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
  convTermT₁ Shp A≡B t = {!!}
  
  convTermT₂ : ∀ {k k′ A B t} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
           → ShapeView Γ k k′ A B [A] [B]
           → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
           → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
           → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
  convTermT₂ Shp A≡B t = {!!}

  -- Irrelevance for type equality
  irrelevanceEq₃ : ∀ {A B k k′ k″} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A) (r : Γ / lε ⊩⟨ k″ ⟩ B)
                → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
  irrelevanceEq₃ p q r A≡B = irrelevanceEqT₃ (combine (goodCasesRefl q p) (goodCases p r A≡B)) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq₃′ : ∀ {A A′ B k k′ k″} (eq : A PE.≡ A′)
                   (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′) (r : Γ / lε ⊩⟨ k″ ⟩ B)
                 → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A′ ≡ B / q
  irrelevanceEq₃′ PE.refl p q r A≡B = irrelevanceEq₃ p q r A≡B

  irrelevanceEqT₃ :  ∀ {A B k k′ k″} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {r : Γ / lε ⊩⟨ k″ ⟩ B}
                       → ShapeView₃ Γ k k′ k″ A A B p q r
                       → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q → Γ / lε ⊩⟨ k ⟩ A ≡ B / p
  irrelevanceEqT₃ (ℕᵥ D D′ D″) A≡B = A≡B
  irrelevanceEqT₃ (𝔹ᵥ D D′ D″) A≡B = A≡B
--   irrelevanceEqT₃ (Emptyᵥ D D′ D″) A≡B = A≡B
--  irrelevanceEqT₃ (Unitᵥ D D′ D″) A≡B = A≡B
  irrelevanceEqT₃ (ne (ne K₁ D₁ neK₁ K≡K₁) (ne K D neK _) neB) (ne₌ _ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
                 ne₌ _ M D′ neM K≡M
  irrelevanceEqT₃ (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁) (ne K₂ D₂ neK₂ K≡K₂)) (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) =
    PE.⊥-elim (ne≢αne neK₂ αB (whrDet* (red D₂ , ne neK₂) (red B⇒B' , αₙ αB)))
  irrelevanceEqT₃ {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
                                          (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                          (Bᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                  with B-PE-injectivity W (whrDet* ( D′ , ⟦ W ⟧ₙ) (red D₂ , ⟦ W ⟧ₙ))
  irrelevanceEqT₃ {Γ = Γ} {lε = lε} {k = k} {k′ = k′} (Bᵥ W (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
                                          (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                          (Bᵣ _ _ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                  | PE.refl , PE.refl =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity W ΠFG≡ΠF₁G₁
    in  B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ (PE.subst (λ x → Γ / lε ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {m} {ρ} {Δ} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ →
             irrelevanceEq₃′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                             ([F]₁ [ρ] ⊢Δ) ([F]₂ {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
           (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
                  F₁≡F' = irrelevanceEq₃′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                                         ([F]₁ [ρ] ⊢Δ) ([F]₂ {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₂ = convTermT₁ {A = wk ρ F₁} (goodCases ([F]₁ [ρ] ⊢Δ) ([F]₂ {≤ε = ≤ε} [ρ] ⊢Δ) F₁≡F')
                                    F₁≡F' [a]₁ -- irrelevanceTerm′ 
                                         -- ([F]₁ [ρ] ⊢Δ) ([F]₂ {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
              in irrelevanceEq₃′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G]₂ [ρ] ⊢Δ [a]₂) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT₃ (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
                      (Bᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
                              (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) =
                  PE.⊥-elim (B≢αne W αB (whrDet* (red D₂ , ⟦ W ⟧ₙ) (red B⇒B' , αₙ αB)))
  irrelevanceEqT₃ (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _) UB) A≡B = A≡B
  irrelevanceEqT₃ (emb⁰¹¹ x) A≡B = irrelevanceEqT₃ x A≡B
  irrelevanceEqT₃ (emb¹⁰¹ x) A≡B = irrelevanceEqT₃ x A≡B
  irrelevanceEqT₃ (emb¹¹⁰ x) A≡B = irrelevanceEqT₃ x A≡B
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (Uᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (ℕᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqT₃ (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl =
      irrelevanceEqT₃ (combine (goodCasesRefl [A]t tB) (goodCases tB [C]t tA≡B)) tA≡B ,
      irrelevanceEqT₃ (combine (goodCasesRefl [A]f fB) (goodCases fB [C]f fA≡B)) fA≡B
  irrelevanceEqT₃ (ϝᵣ-l A⇒A' αA (emb 0<1 [B]) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    irrelevanceEqT₃ (combine (goodCasesRefl (ϝᵣ _ A⇒A' αA [A]t [A]f) [B]) (goodCases [B] [C] A≡B)) A≡B 
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (Uᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B) =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (ℕᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B) =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (𝔹ᵣ D) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B) =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (ne′ K D neK K≡K) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B) =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B) =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqT₃ (ϝᵣ-m {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | PE.refl | PE.refl | PE.refl =
    irrelevanceEqT₃ (combine (goodCasesRefl tB [B]t) (goodCases [B]t [C]t tA≡B)) tA≡B ,
    irrelevanceEqT₃ (combine (goodCasesRefl fB [B]f) (goodCases [B]f [C]f fA≡B)) fA≡B
  irrelevanceEqT₃ (ϝᵣ-m A⇒A' αA (emb 0<1 [A]) [C] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B =
    irrelevanceEqT₃ (combine (goodCasesRefl [A] (ϝᵣ _ A⇒A' αA [B]t [B]f)) (goodCases (ϝᵣ _ A⇒A' αA [B]t [B]f) [C] A≡B)) A≡B 
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    with goodCasesRefl [A] [B] 
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) PE.refl
    | Uᵥ UA UB = PE.⊥-elim (U≢αne αC (whnfRed* (red C⇒C') Uₙ))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (⊩ℕ≡ A C C⇒ℕ)
    | ℕᵥ ℕA ℕB = PE.⊥-elim (ℕ≢αne αC (whrDet* (C⇒ℕ , ℕₙ) (red C⇒C' , αₙ αC)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB with whrDet* (red C⇒C' , αₙ αC) (red C⇒C'' , αₙ αC')
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl with αNeutralHProp αC αC'
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl
      with TyLogℕ (τwfRed* ℕA) [A]t with TyLogℕ (τwfRed* ℕA) [A]f with TyLogℕ (τwfRed* ℕB) [B]t with TyLogℕ (τwfRed* ℕB) [B]f
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | noemb ℕAf , PE.refl |
      noemb ℕBt , PE.refl | noemb ℕBf , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | noemb ℕAf , PE.refl |
      noemb ℕBt , PE.refl | emb 0<1 (noemb ℕBf) , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | noemb ℕAf , PE.refl |
      emb 0<1 (noemb ℕBt) , PE.refl | noemb ℕBf , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | noemb ℕAf , PE.refl |
      emb 0<1 (noemb ℕBt) , PE.refl | emb 0<1 (noemb ℕBf) , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | emb 0<1 (noemb ℕAf), PE.refl |
      noemb ℕBt , PE.refl | noemb ℕBf , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | emb 0<1 (noemb ℕAf) , PE.refl |
      noemb ℕBt , PE.refl | emb 0<1 (noemb ℕBf) , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | emb 0<1 (noemb ℕAf) , PE.refl |
      emb 0<1 (noemb ℕBt) , PE.refl | noemb ℕBf , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | emb 0<1 (noemb ℕAf) , PE.refl |
      emb 0<1 (noemb ℕBt) , PE.refl | emb 0<1 (noemb ℕBf) , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | noemb ℕAt , PE.refl | noemb ℕAf , PE.refl |
      noemb ℕBt , PE.refl | emb 0<1 (noemb ℕBf) , PE.refl = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | emb 0<1 (noemb ℕAt) , PE.refl | noemb ℕAf , PE.refl |
      noemb ℕBt , PE.refl | noemb ℕBf , PE.refl =
      ϝ⊩ℕ≡ mε C⇒C'' αC' (irrelevanceEqT₃ (combine (goodCasesRefl [A]t [B]t) (goodCases [B]t [C]t tA≡ℕ)) tA≡ℕ) {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (ϝ⊩ℕ≡ mε C⇒C'' αC' tA≡ℕ fA≡ℕ)
    | ℕᵥ ℕA ℕB | PE.refl | PE.refl | PE.refl | K , PE.refl | K' , PE.refl |
      K'' , PE.refl | K''' , PE.refl = ϝ⊩ℕ≡ mε C⇒C'' αC' (Convℕ K'' {!!}) {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B 
    | 𝔹ᵥ 𝔹A 𝔹B = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | emb⁰¹ x = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B 
    | emb¹⁰ x = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K₁≡K₁) = {!!}
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (Uᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (ℕᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (emb 0<1 [B']) [A']t [A']f [B']t [B']f tAB fAB =
    irrelevanceEqT₃ (combine (goodCasesRefl (ϝᵣ _ A⇒A' αA [A']t [A']f) [B']) (goodCases [B'] (ϝᵣ _ C⇒C' αC [C]t [C]f) A≡B)) A≡B
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-r {n = n} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l {n = m} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl | PE.refl | PE.refl  with decidEqNat n m
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-l {nε = mε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl | PE.refl | PE.refl  | TS.inj₁ PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-l {nε = mε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl | PE.refl | PE.refl  | TS.inj₁ PE.refl | PE.refl =
    irrelevanceEqT₃ (combine (goodCasesRefl [A']t tB) (goodCases tB [C]t tA≡B)) tA≡B ,
    irrelevanceEqT₃ (combine (goodCasesRefl [A']f fB) (goodCases fB [C]f fA≡B)) fA≡B
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-l {nε = mε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A']t [A']f [B']t [B']f tAB fAB 
    | PE.refl | PE.refl | PE.refl  | TS.inj₂ noteq =
      let kε = λ b → NotInThereNat _ nε _ b (DifferentDifferentNat _ _ λ e → noteq e)
          ϝε = λ b → (ϝᵣ (kε b) (τwfRed* {_} {_} {_} {_} {_} {_} {_} {_} {mε} C⇒C') (αNeNotIn (kε b) αC)
                         (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [C]t)
                         (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [C]f))
                         in
    irrelevanceEqT₃ (combine (goodCasesRefl [A']t tB) (goodCases tB (ϝε Btrue) tA≡B)) tA≡B ,
    irrelevanceEqT₃ (combine (goodCasesRefl [A']f fB) (goodCases fB (ϝε Bfalse) fA≡B)) fA≡B
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r A⇒A' αA (Uᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r A⇒A' αA (ℕᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r A⇒A' αA (𝔹ᵣ D) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r A⇒A' αA (ne′ K D neK K≡K) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A']t [A']f [B']t [B']f tAB fAB =
    PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) A≡B
    | ϝᵣ-r B⇒B' αB (emb 0<1 [A']) [A']t [A']f [B']t [B']f tAB fAB =
    irrelevanceEqT₃ (combine (goodCasesRefl [A'] [B]) (goodCases [B] (ϝᵣ _ C⇒C' αC [C]t [C]f) A≡B)) A≡B
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl with αNeutralHProp αA αB
  irrelevanceEqT₃ (ϝᵣ-r C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r {nε = nε} B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-r {n = n} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r {n = m} B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl | PE.refl | PE.refl  with decidEqNat n m
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r {nε = mε} B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl | PE.refl | PE.refl  | TS.inj₁ PE.refl with NotInLConNatHProp _ _ mε nε
  irrelevanceEqT₃ (ϝᵣ-r {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r {nε = mε} B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl | PE.refl | PE.refl  | TS.inj₁ PE.refl | PE.refl =
    irrelevanceEqT₃ (combine (goodCasesRefl tA [B']t) (goodCases [B']t [C]t tA≡B)) tA≡B ,
    irrelevanceEqT₃ (combine (goodCasesRefl fA [B']f) (goodCases [B']f [C]f fA≡B)) fA≡B
  irrelevanceEqT₃ (ϝᵣ-r {n = n} {nε = nε} C⇒C' αC [A] [B] [A]t [A]f [B]t [B]f [C]t [C]f tABC fABC) (tA≡B , fA≡B)
    | ϝᵣ-r {n = m} {nε = mε} B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A']t [A']f [B']t [B']f tAB fAB
    | PE.refl | PE.refl | PE.refl  | TS.inj₂ noteq =
      let kε = λ b → NotInThereNat _ nε _ b (DifferentDifferentNat _ _ λ e → noteq e)
          ϝε = λ b → (ϝᵣ (kε b) (τwfRed* {_} {_} {_} {_} {_} {_} {_} {_} {mε} C⇒C') (αNeNotIn (kε b) αC)
                         (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [C]t)
                         (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (InThere _ inl _ _) _ _) (InHereNat _)) [C]f))
                         in
    irrelevanceEqT₃ (combine (goodCasesRefl tA [B']t) (goodCases [B']t (ϝε Btrue) tA≡B)) tA≡B ,
    irrelevanceEqT₃ (combine (goodCasesRefl fA [B']f) (goodCases [B']f (ϝε Bfalse) fA≡B)) fA≡B
  -- irrelevanceEqT₃ Shp A≡B = {!!}

  irrelevanceEqT″ : ∀ {A B k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A}
                       → ShapeView Γ k k′ A A p q
                       → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
  irrelevanceEqT″ Shp A≡B = {!!}


escapeEqLog : ∀ {k A B} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
            → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
            → Γ / lε ⊩⟨ k ⟩ B
escapeEqLog (Uᵣ′ k′ k< ⊢Γ) PE.refl = {!!}
escapeEqLog {k = k} (ℕᵣ D) A=B  = {!!}
escapeEqLog {k = k} (𝔹ᵣ D) A=B  = {!!}
-- escapeEqLog (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
-- escapeEqLog (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
escapeEqLog {k = k} (ne neA) A=B = {!!}
escapeEqLog {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
                 Bᵣ W (Bᵣ F′ G′ [ {!!} , {!!} , D′ ] {!!} {!!} {!!}
                     (λ {m} {l'} {f<} {lε'} {ρ} {Δ} [ρ] ⊢Δ → escapeEqLog ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
                     (λ {m} {ρ} {Δ} {a} {l'} {f<} {lε'} [ρ] ⊢Δ [a] →
                     -- irrelevanceEq₃′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
                      --                   ([F]₁ [ρ] ⊢Δ) ([F]₂ {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                     let js = irrelevanceEq₃ {!!} {!!} {!!} {!!} in
                     escapeEqLog ([G] [ρ] ⊢Δ (convTermT₁ (goodCases (escapeEqLog ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)) ([F] [ρ] ⊢Δ) js) {!!} [a])) {!!}) {!!})
escapeEqLog {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) = ϝᵣ {!!} B⇒B' αB {!!} {!!}
escapeEqLog (emb 0<1 A) A≡B = emb 0<1 (escapeEqLog A A≡B)
escapeEqLog (ϝᵣ mε A⇒B αB tB fB) ( x , y ) = {!!}

-- mutual
--   -- Irrelevance for type equality
--   irrelevanceEq : ∀ {A B k k′} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A)
--                 → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
--   irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

--   -- Irrelevance for type equality with propositionally equal first types
--   irrelevanceEq′ : ∀ {A A′ B k k′} (eq : A PE.≡ A′)
--                    (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
--                  → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A′ ≡ B / q
--   irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

--   -- Irrelevance for type equality with propositionally equal types
--   irrelevanceEq″ : ∀ {A A′ B B′ k k′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
--                     (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A′)
--                   → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A′ ≡ B′ / q
--   irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B


--   -- Irrelevance for type equality with propositionally equal types and
--   -- a lifting of propositionally equal types
--   irrelevanceEqLift″ : ∀ {A A′ B B′ C C′ k k′}
--                         (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
--                         (p : Γ ∙ C / lε ⊩⟨ k ⟩ A) (q : Γ ∙ C′ / lε ⊩⟨ k′ ⟩ A′)
--                       → Γ ∙ C / lε ⊩⟨ k ⟩ A ≡ B / p → Γ ∙ C′ / lε ⊩⟨ k′ ⟩ A′ ≡ B′ / q
--   irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

--   irrelevanceEqTW : ∀ W W' {A B k k′} [A] [A']
--                        → Γ / lε ⊩⟨ k ⟩ A ≡ B / Bᵣ W [A] → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / Bᵣ W' [A']
--   irrelevanceEqTW {Γ = Γ} {lε = lε} BΠ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                                       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--     let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ BΠ ⟧ₙ) (red D₁ , ⟦ BΠ ⟧ₙ)
--         F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
--     in  B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ (PE.subst (λ x → Γ / lε ⊢ x ≅ ⟦ BΠ ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
--            (λ {m} {ρ} {Δ} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ →
--              irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
--                                      ([F]₁ [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
--            (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
--               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
--                                          ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
--               in irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
--                                ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
--   irrelevanceEqTW {Γ = Γ} {lε = lε} BΠ BΠ {_} {_} {⁰} {⁰} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--                  (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) =
--      Bϝ _ B⇒B' αB [A]t [A]f tA≡B fA≡B
--  --     (Bᵣ F₁ G₁ (τwfRed* D₁) (τTy _ _ _ _ ⊢F₁) (τTy _ _ _ _ ⊢G₁) (≅-τ A≡A₁) [F]₁
--  --          (λ {m = m₁} {ρ} {Δ} {a} {l'} {≤ε} → [G]₁ {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext₁) tA≡B
--  --          (irrelevanceEqTW BΠ BΠ [A]f (Bᵣ F₁ G₁ (τwfRed* D₁) (τTy _ _ _ _ ⊢F₁) (τTy _ _ _ _ ⊢G₁) (≅-τ A≡A₁) [F]₁
--  --                                     (λ {m = m₁} {ρ} {Δ} {a} {l'} {≤ε} →  [G]₁ {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext₁) fA≡B)
--   irrelevanceEqTW {Γ = Γ} {lε = lε} W W' (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                                       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) = {!!}
--   irrelevanceEqTW {Γ = Γ} {lε = lε} W W' (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                               (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
--                  (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) = {!!}
                 
--   -- Helper for irrelevance of type equality using shape view
--   irrelevanceEqT : ∀ {A B k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A}
--                        → ShapeView Γ k k′ A A p q
--                        → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
--   irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
--   irrelevanceEqT (𝔹ᵥ D D′) A≡B = A≡B
-- --   irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
-- --  irrelevanceEqT (Unitᵥ D D′) A≡B = A≡B
--   irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ _ M D′ neM K≡M)
--                  rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
--     ne₌ _ M D′ neM K≡M
--   irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) = {!!}
--   irrelevanceEqT {Γ = Γ} {lε = lε} (Bᵥ W BA BA') A≡B = irrelevanceEqTW W W BA BA' A≡B -- {!!} (irrelevanceEqT (τShapeView {!!}) tA≡B) {!!}
--   irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
--   irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
--   irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B)
--     | PE.refl | PE.refl | PE.refl = irrelevanceEqT (goodCasesRefl [A]t tB) tA≡B , irrelevanceEqT (goodCasesRefl [A]f fB) fA≡B
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB) (tA≡B , fA≡B) = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B =
--     PE.⊥-elim (U≢αne αB (whnfRed* (red B⇒B') Uₙ))
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (emb 0<1 [B]) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
--   irrelevanceEqT (ϝᵣ-r B⇒B' αB (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB) A≡B = {!!}
