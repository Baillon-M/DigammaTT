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


-- mutual
--   irrelevanceTerm : ∀ {A t k k′ l' l''} {lε' : ⊢ₗ l'} {lε'' : ⊢ₗ l''} (≤ε : l ≤ₗ l'') (≤ε' : l' ≤ₗ l'') (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε' ⊩⟨ k′ ⟩ A)
--                   → (H : ∀ k‴ l‴ (lε‴ : ⊢ₗ l‴) (≤ε‴ : l' ≤ₗ l‴) → (r : Γ / lε‴ ⊩⟨ k‴ ⟩ A))
--                   → (∀ k‴ l‴ (lε‴ : ⊢ₗ l‴) (≤ε‴ : l' ≤ₗ l‴) → Γ / lε' ⊩⟨ k′ ⟩ t ∷ A / q → Γ / lε‴ ⊩⟨ k‴ ⟩ A / (H k‴ l‴ lε‴ ≤ε‴))
--                   → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q

mutual


--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t k k′} (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε ⊩⟨ k′ ⟩ A)
                  → Γ / lε ⊩⟨ k ⟩ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = {!!} -- irrelevanceTermT (goodCasesRefl p q) t

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
  irrelevanceTermT₀ : ∀ {A t k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ A / p}
                         → ShapeView Γ k k′ A A p q A≡B
                         → Γ / lε ⊩⟨ k ⟩ t ∷ A / p
                         → (μTy q) PE.≡ 0
                         → (μConv A≡B) PE.≡ 0
                         → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTermT₀ (ℕᵥ D D′ A≡B) t eq₁ eq₂ = t
  irrelevanceTermT₀ (𝔹ᵥ D D′ A≡B) t eq₁ eq₂ = t
--   irrelevanceTermT₀ (Emptyᵥ D D′) t eq₁ eq₂ eq₃ = t
--   irrelevanceTermT₀ (Unitᵥ D D′) t eq₁ eq₂ eq₃ = t
  irrelevanceTermT₀ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) (neₜ k d nf) eq₁ eq₂
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT₀ (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁) A≡B) (neₜ k d nf) eq₁ eq₂
    | PE.refl = neₜ k d nf
  irrelevanceTermT₀ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) (neϝ tk fk) eq₁ eq₂
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT₀ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) (neϝ tk fk) eq₁ eq₂
    | PE.refl  = neϝ tk fk
  irrelevanceTermT₀ {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
                   (Πₜ ⊢f f≡f [f] [f]₁) eq₁ eq₂ =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
    in  Πₜ (PE.subst (λ x → Γ / lε ⊢ t ∷ x) ΠFG≡ΠF₁G₁ ⊢f) (PE.subst (λ x → Γ / lε ⊢ t ≅ t ∷ x) ΠFG≡ΠF₁G₁ f≡f)
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
  irrelevanceTermT₀ {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
                   (Σₜ p d pProd p≅p [fst] [snd]) eq₁ eq₂ =
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
  irrelevanceTermT₀ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁) A≡B) t eq₁ eq₂ = t
  irrelevanceTermT₀ (emb⁰¹ x) t eq₁ ()
  irrelevanceTermT₀ (emb¹⁰ x) t () eq₂
  irrelevanceTermT₀ (ϝᵣ-l [A] [B] [A]t [A]f [B]t [B]f tA≡B fA≡B tAB fAB) t eq₁ ()
  irrelevanceTermT₀ (ϝᵣ-r [A] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) t () eq₂

  irrelevanceTermT₁ : ∀ {A t k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ A / p}
                        → (N : Nat)
                        → ShapeView Γ k k′ A A p q A≡B
                        → Γ / lε ⊩⟨ k ⟩ t ∷ A / p
                        → (((μTy q) + (μConv A≡B)) ≤ N)
                        → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTermT₁ {k = k} {k′ = k′} 0 (ℕᵥ D D′ A≡B) t (≤-0 0) = irrelevanceTermT₀ {k = k} {k′ = k′} (ℕᵥ D D′ A≡B) t PE.refl PE.refl
  irrelevanceTermT₁ (1+ N) (ℕᵥ D D′ A≡B) t (≤-0 _) = {!!}
  irrelevanceTermT₁ {k = k} {k′ = k′} 0 (𝔹ᵥ D D′ A≡B) t (≤-0 0) = irrelevanceTermT₀ {k = k} {k′ = k′} (𝔹ᵥ D D′ A≡B) t PE.refl PE.refl
  irrelevanceTermT₁ (1+ N) (𝔹ᵥ D D′ A≡B) t (≤-0 _) = {!!}
  irrelevanceTermT₁ 0 (Uᵥ UA UB A≡B) t (≤-0 0) = irrelevanceTermT₀ (Uᵥ UA UB A≡B) t PE.refl PE.refl
  irrelevanceTermT₁ (1+ N) (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁) A≡B) t (≤-0 _) = {!!}
  irrelevanceTermT₁ {k = k} {k′ = k′} 0 (Bᵥ W BA BB A≡B) t (≤-0 0) = irrelevanceTermT₀ (Bᵥ W BA BB A≡B) t PE.refl PE.refl
  irrelevanceTermT₁ (1+ N) (Bᵥ W BA BB A≡B) t (≤-0 _) = {!!}
  irrelevanceTermT₁ {k = k} {k′ = k′} 0 (ne neA neB A≡B) t (≤-0 0) =
    irrelevanceTermT₀ {k = k} {k′ = k′} (ne neA neB A≡B) t PE.refl PE.refl
  irrelevanceTermT₁ (1+ N) (ne neA neB A≡B) t (≤-0 _) = {!!}
  irrelevanceTermT₁ {q = q} {A≡B = ⊩¹≡emb 0<1 p A≡B} N (emb⁰¹ x) t N<
    with ≤-trans (≤₊-s-swap (μTy q) (μConv A≡B)) N<
  irrelevanceTermT₁ {q = q} (1+ N) (emb⁰¹ x) t N<
    | (≤-s K<) = irrelevanceTermT₁ N x t K<
  irrelevanceTermT₁ (1+ N) (emb¹⁰ x) t (≤-s N<) = irrelevanceTermT₁ N x t N<
  irrelevanceTermT₁ N (ϝᵣ-l [A] [B] [A]t [A]f [B]t [B]f tA≡B fA≡B tAB fAB) t N<
    with ≤-trans (≤₊-s-swap (μTy [B]) (max (μConv tA≡B) (μConv fA≡B))) N<
  irrelevanceTermT₁ (1+ N) (ϝᵣ-l [A] [B] [A]t [A]f [B]t [B]f tA≡B fA≡B tAB fAB) t N<
    | ≤-s K< = {!!}
  irrelevanceTermT₁ (1+ N) (ϝᵣ-r [A] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) t (≤-s N<) =
    irrelevanceTermT₁ N tAB {!!} (≤-trans {!!} N<) , {!!}

--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceTermT₀ (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--     irrelevanceTermT₀ (goodCasesRefl [A]t tB) tu≡v , irrelevanceTermT₀ (goodCasesRefl [A]f fB) fu≡v
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceTermT₀ (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                    (tu≡v , fu≡v) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceTermT (ϝᵣ-l {nε = nε} A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                    (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--       irrelevanceTermT (goodCasesRefl [A]t tB) tu≡v , irrelevanceTermT (goodCasesRefl [A]f fB) fu≡v
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceTermT (ϝᵣ-r {nε = nε} A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tA , fA)
--     | PE.refl | PE.refl | PE.refl =
--     irrelevanceTermT (goodCasesRefl tB [B]t) tA , irrelevanceTermT (goodCasesRefl fB [B]f) fA
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceTermT (ϝᵣ-r {nε = nε} A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tA , fA)
--     | PE.refl | PE.refl | PE.refl =
--     irrelevanceTermT (goodCasesRefl tB [B]t) tA , irrelevanceTermT (goodCasesRefl fB [B]f) fA 

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
  irrelevanceEqTermT : ∀ {A t u} {k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ A / p}
                           → ShapeView Γ k k′ A A p q A≡B
                           → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (ℕᵥ D D′ A≡B) t≡u = t≡u
  irrelevanceEqTermT (𝔹ᵥ D D′ A≡B) t≡u = t≡u
--   irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
--   irrelevanceEqTermT (Unitᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) ne=
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁) A≡B) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁) A≡B) (ne₌ϝ tk≡k' fk≡k')
    | PE.refl = ne₌ϝ tk≡k' fk≡k'
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
                     (Πₜ₌ f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
        [A]         = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ (PE.subst (λ x → Γ / lε ⊢ t ≅ u ∷ x) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                          ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a]))
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
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
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁) A≡B) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (ϝᵣ-l [A] [B] [A]t [A]f [B]t [B]f tA≡B fA≡B tAB fAB) t = {!!}
  irrelevanceEqTermT (ϝᵣ-r [A] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) t = irrelevanceEqTermT tAB {!!} , irrelevanceEqTermT fAB {!!} 
  
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqTermT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--     irrelevanceEqTermT (goodCasesRefl [A]t tB) tu≡v , irrelevanceEqTermT (goodCasesRefl [A]f fB) fu≡v
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v) =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqTermT (ϝᵣ-l {nε = nε} A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqTermT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--     irrelevanceEqTermT (goodCasesRefl [A]t tB) tu≡v , irrelevanceEqTermT (goodCasesRefl [A]f fB) fu≡v
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqTermT (ϝᵣ-r {nε = nε} A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--      irrelevanceEqTermT (goodCasesRefl tB [B]t) tu≡v , irrelevanceEqTermT (goodCasesRefl fB [B]f) fu≡v
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqTermT (ϝᵣ-r {nε = nε} A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (tu≡v , fu≡v)
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqTermT (ϝᵣ-r A⇒A' A⇒A'' αA αA' (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                      (tu≡v , fu≡v)
--     | PE.refl | PE.refl | PE.refl =
--      irrelevanceEqTermT (goodCasesRefl tB [B]t) tu≡v , irrelevanceEqTermT (goodCasesRefl fB [B]f) fu≡v
--   -- irrelevanceEqTermT (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) t≡u = {!!}

--   -- Irrelevance for type equality with propositionally equal second types
-- irrelevanceEqR′ : ∀ {A B B′ k} (eqB : B PE.≡ B′) (p : Γ / lε ⊩⟨ k ⟩ A)
--                 → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k ⟩ A ≡ B′ / p
-- irrelevanceEqR′ PE.refl p A≡B = A≡B

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
           
--   -- Helper for irrelevance of type equality using shape view
--   irrelevanceEqT : ∀ {A B k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {A≡A : Γ / lε ⊩⟨ k ⟩ A ≡ A / p}
--                        → ShapeView Γ k k′ A A p q A≡A
--                        → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ A ≡ B / q
--   irrelevanceEqT (ℕᵥ D D′ A≡A) (⊩¹≡ℕ _ A≡B) = ⊩¹≡ℕ _ A≡B
--   irrelevanceEqT (𝔹ᵥ D D′ A≡A) (⊩¹≡𝔹 _ A≡B) = ⊩¹≡𝔹 _ A≡B
-- --   irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
-- --  irrelevanceEqT (Unitᵥ D D′) A≡B = A≡B
--   irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁) A≡A) (⊩¹≡ne _ (ne₌ M D′ neM K≡M))
--                  with whrDet* (red D , ne neK) (red D₁ , ne neK₁)
--   irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁) A≡A) (⊩¹≡ne _ (ne₌ M D′ neM K≡M))
--                  | PE.refl = 
--                  ⊩¹≡ne _ (ne₌ M D′ neM K≡M)
--   irrelevanceEqT {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A=A)
--                                        (⊩¹≡B W _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) =
--                  let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W ⟧ₙ)
--                      F≡F₁ , G≡G₁ = B-PE-injectivity W ΠFG≡ΠF₁G₁
--     in  ⊩¹≡B _ _ (B₌ F′ G′ D′ (PE.subst (λ x → Γ / lε ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
--            (λ {m} {ρ} {Δ} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ →
--              irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ)
--                                      ([F]₁ [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
--            (λ {_} {ρ} {_} {_} {l'} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a]₁ →
--               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
--                                          ([F]₁ [ρ] ⊢Δ) ([F] {_} {l'} {≤ε} [ρ] ⊢Δ) [a]₁
--               in irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
--                                ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a])))
--   irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _) A≡A) (⊩¹≡U _ A≡B) = ⊩¹≡U _ A≡B
--   irrelevanceEqT {p = emb 0<1 p} {q = q} AB (⊩¹≡emb _ _ A≡B) = irrelevanceEqT (goodCasesRefl p q) A≡B
--   irrelevanceEqT (emb¹⁰ x) A≡B = ⊩¹≡emb _ _ (irrelevanceEqT x A≡B)
--   irrelevanceEqT {q = [A']} AB (⊩¹≡ϝ-r B⇒B' αB' [A] tA fA tA≡B fA≡B) =
--     ⊩¹≡ϝ-r B⇒B' αB' [A'] _ _ (irrelevanceEqT (goodCasesRefl tA (τTyLog [A'])) tA≡B)
--                              (irrelevanceEqT (goodCasesRefl fA (τTyLog [A'])) fA≡B)
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqT (ϝᵣ-l {nε = nε} A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (ϝᵣ mε B⇒B' αB tB fB) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl | PE.refl =
--       ⊩¹≡ϝ-l B⇒B' αB tB fB (irrelevanceEqT (goodCasesRefl [A]t tB) tA≡B')
--                            (irrelevanceEqT (goodCasesRefl [A]f fB) fA≡B')
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Uᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ℕᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (ℕ≢αne αA (whrDet* (red D , ℕₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (𝔹ᵣ D)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (𝔹≢αne αA (whrDet* (red D , 𝔹ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ne′ K D neK K≡K)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B') =
--     PE.⊥-elim (B≢αne W αA (whrDet* (red D , ⟦ W ⟧ₙ) (red A⇒A' , αₙ αA)))
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqT (ϝᵣ-l {nε = nε} A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqT (ϝᵣ-l A⇒A' αA (emb 0<1 (ϝᵣ mε B⇒B' αB tB fB)) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl | PE.refl =
--       ⊩¹≡emb _ _ (⊩¹≡ϝ-l B⇒B' αB tB fB (irrelevanceEqT (goodCasesRefl [A]t tB) tA≡B')
--                                        (irrelevanceEqT (goodCasesRefl [A]f fB) fA≡B'))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (Uᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (⊩¹≡U _ A≡B) =
--     PE.⊥-elim (U≢αne αB (whnfRed* (red B⇒B') Uₙ))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (ℕᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (⊩¹≡ℕ _ A≡B) =
--     PE.⊥-elim (ℕ≢αne αB (whrDet* (red D , ℕₙ) (red B⇒B' , αₙ αB)))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (𝔹ᵣ D) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) (⊩¹≡𝔹 _ A≡B) = 
--     PE.⊥-elim (𝔹≢αne αB (whrDet* (red D , 𝔹ₙ) (red B⇒B' , αₙ αB)))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (ne′ K D neK K≡K) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ne _ A≡B) =
--     PE.⊥-elim (ne≢αne neK αB (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB)))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡B _ _ A≡B) =
--     PE.⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (red B⇒B' , αₙ αB)))
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     with whrDet* (red A⇒A' , αₙ αA) (red B⇒B' , αₙ αB)
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl with αNeutralHProp αA αB
--   irrelevanceEqT (ϝᵣ-r {nε = nε} B⇒B' B⇒B'' αB αB' (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl with NotInLConNatHProp _ _ mε nε
--   irrelevanceEqT (ϝᵣ-r B⇒B' B⇒B'' αB αB' (ϝᵣ mε A⇒A' αA tA fA) [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B)
--                  (⊩¹≡ϝ-l A⇒A' αA' tA fA tA≡B' fA≡B')
--     | PE.refl | PE.refl | PE.refl =
--       ⊩¹≡ϝ-l B⇒B' αB [B]t [B]f (irrelevanceEqT (goodCasesRefl _ _) tA≡B')
--                                (irrelevanceEqT (goodCasesRefl _ _) fA≡B')
