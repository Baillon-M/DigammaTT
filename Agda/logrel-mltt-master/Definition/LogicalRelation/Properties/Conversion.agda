{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Conversion {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
-- open import Definition.LogicalRelation.Irrelevance

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l

-- Conversion of syntactic reduction closures.
convRed:*: : ∀ {t u A B} → Γ / lε ⊢ t :⇒*: u ∷ A → Γ / lε ⊢ A ≡ B → Γ / lε ⊢ t :⇒*: u ∷ B
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]

  -- Irrelevance for type equality with propositionally equal second types
irrelevanceEqR′ : ∀ {A B B′ k} (eqB : B PE.≡ B′) (p : Γ / lε ⊩⟨ k ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k ⟩ A ≡ B′ / p
irrelevanceEqR′ PE.refl p A≡B = A≡B


mutual
  -- Helper function for conversion of terms converting from left to right.
  convTermT₁ : ∀ {k k′ A B t} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
             → ShapeView Γ k k′ A B [A] [B]
             → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
             → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
             → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (𝔹ᵥ D D′) A≡B t = t
  -- convTermT₁ (Emptyᵥ D D′) A≡B t = t
  -- convTermT₁ (Unitᵥ D D′) A≡B t = t
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K≡K₁ = PE.subst (λ x → _  / _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ k (convRed:*: d K≡K₁)
            (neNfₜ neK₂ (conv ⊢k K≡K₁) (~-conv k≡k K≡K₁))
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ k d (neNfϝ ⊢k αk tk fk)) = {!!}
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁))
             (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) t = {!!}
  convTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
    in  Πₜ f (convRed:*: d ΠFG≡ΠF₁G₁) funcF (≅-conv f≡f ΠFG≡ΠF₁G₁)
           (λ {_} {ρ} {Δ : Con Term _} {a b} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G′] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
          (λ {_} {ρ} {Δ : Con Term _} {a} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] →
             let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                   (PE.sym G₁≡G′))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G′] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₁ {Γ = Γ} {lε = lε} {k = k} {k′ = k′} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                 (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Σₜ f d pProd f≡f [fst] [snd]) =
    let ΣF₁G₁≡ΣF′G′   = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
                             (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ / lε ⊩⟨ k ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [fst]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [fst]
        G≡G₁ = PE.subst (λ x → Γ / lε ⊩⟨ k ⟩ wk (lift id) G [ fst f ] ≡ wk (lift id) x [ fst f ] / [G] Wk.id ⊢Γ [fst])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [fst])
        [snd]₁ = convTerm₁ ([G] Wk.id ⊢Γ [fst]) ([G]₁ Wk.id (wf ⊢F₁) [fst]₁) G≡G₁ [snd]
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) pProd (≅-conv f≡f ΣFG≡ΣF₁G₁)
          [fst]₁ [snd]₁
  convTermT₁ {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) t = {!!}
  convTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) = {!!}
  convTermT₁ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) A≡B t = {!!}

  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {k k′ A B t} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
           → ShapeView Γ k k′ A B [A] [B]
           → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
           → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
           → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (𝔹ᵥ D D′) A≡B t = t
  -- convTermT₂ (Emptyᵥ D D′) A≡B t = t
  -- convTermT₂ (Unitᵥ D D′) A≡B t = t
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _  / _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ k d (neNfϝ ⊢k αk tk fk)) = {!!}
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁))
             (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) t = {!!}
  convTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ f (convRed:*: d (sym ΠFG≡ΠF₁G₁)) funcF (≅-conv f≡f (sym ΠFG≡ΠF₁G₁))
           (λ {_} {ρ} {Δ : Con Term _} {a b} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ {≤ε = ≤ε} [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
           (λ {_} {ρ} {Δ : Con Term _} {a} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ {≤ε = ≤ε} [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₂ {Γ = Γ} {lε = lε} {k = k} {k′ = k′} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Σₜ f d pProd f≡f [fst]₁ [snd]₁) =
    let ΣF₁G₁≡ΣF′G′   = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ / lε ⊩⟨ k ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [fst] = (convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst]₁)
        G≡G₁ = PE.subst (λ x → Γ / lε ⊩⟨ k ⟩ wk (lift id) G [ fst f ] ≡ wk (lift id) x [ fst f ] / [G] Wk.id ⊢Γ [fst])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [fst])
        [snd] = (convTerm₂ ([G] Wk.id ⊢Γ [fst]) ([G]₁ Wk.id ⊢Γ₁ [fst]₁) G≡G₁ [snd]₁)
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) pProd (≅-conv f≡f (sym ΣFG≡ΣF₁G₁))
           [fst] [snd]
  convTermT₂ {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) t = {!!}
  convTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) = {!!}
  convTermT₂ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) A≡B t = {!!}

  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {A B t k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
            → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
            → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
            → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {A B t k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
          → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
          → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
          → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
  -- NOTE: this would be easier to define by mutual induction with symEq (which needs conversion),
  -- rather than by defining everything from scratch for both left-to-right and right-to-left,
  -- but with the mutual definition termination checking fails in Agda.
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left
  -- with some propositionally equal types.
  convTerm₂′ : ∀ {A B B′ t k k′} → B PE.≡ B′
          → ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
          → Γ / lε ⊩⟨ k ⟩  A ≡ B′ / [A]
          → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
          → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
  convTerm₂′ PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  -- Helper function for conversion of term equality converting from left to right.
  convEqTermT₁ : ∀ {k k′ A B t u} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
               → ShapeView Γ k k′ A B [A] [B]
               → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
               → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
               → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (𝔹ᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₁ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _  / _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ₌ k m d d' (⊩neNfϝ-l αk [k'] tk≡k' fk≡k')) = {!!}
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ₌ k m d d' (⊩neNfϝ-r [k] αk' tk≡k' fk≡k')) = {!!}
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁))
             (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) t = {!!}
  convEqTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d ΠFG≡ΠF₁G₁) (convRed:*: d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {_} {ρ} {Δ : Con Term _} {a} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] →
               let F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] {≤ε = ≤ε} [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G′] [ρ] ⊢Δ [a]₁)
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
    let [A] = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ (λ {m} {l'} {≤ε} {lε'} → [F]₁ {m} {l'} {≤ε} {lε'}) [G]₁ G-ext₁
        [A≡B] = B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B (λ {m} {l'} {ρ} {Δ} {≤ε} {lε'} → [F≡F′] {≤ε = ≤ε} {lε'}) [G≡G′]
        ΣF₁G₁≡ΣF′G′ = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [fstp]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstp]
        [fstr]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstr]
        [fst≡]₁ = convEqTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]
        G≡G₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [G] Wk.id ⊢Γ [fstp])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [fstp])
        [snd≡]₁ = convEqTerm₁ ([G] Wk.id ⊢Γ [fstp]) ([G]₁ Wk.id ⊢Γ₁ [fstp]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            pProd rProd (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            [fstp]₁ [fstr]₁ [fst≡]₁ [snd≡]₁
  convEqTermT₁ {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) t≡u = {!!}
  convEqTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) A≡B t≡u = {!!}
  convEqTermT₁ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) A≡B t≡u = {!!}

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {k k′ A B t u} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
             → ShapeView Γ k k′ A B [A] [B]
             → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
             → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
             → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (𝔹ᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₂ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _  / _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ₌ k m d d' (⊩neNfϝ-l αk [k'] tk≡k' fk≡k')) = {!!}
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ [A] M D′ neM K≡M)
             (neₜ₌ k m d d' (⊩neNfϝ-r [k] αk' tk≡k' fk≡k')) = {!!}
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁))
             (ϝ⊩ne≡ mε B⇒B' αB tA≡B fA≡B) t = {!!}
  convEqTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {_} {ρ} {Δ : Con Term _} {a} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] →
               let F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ {≤ε = ≤ε} [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G′] [ρ] ⊢Δ [a])
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Σₜ₌ p r d d′ funcF funcG t≡u [t] [u] [fstp]₁ [fstr]₁ [fst≡]₁ [snd≡]₁) =
    let [A] = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ (λ {m} {l'} {≤ε} {lε'} → [F]₁ {m} {l'} {≤ε} {lε'}) [G]₁ G-ext₁
        [A≡B] = B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B (λ {m} {l'} {ρ} {Δ} {≤ε} {lε'} → [F≡F′] {≤ε = ≤ε} {lε'}) [G≡G′]
        ΣF₁G₁≡ΣF′G′ = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [fstp] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstp]₁
        [fstr] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstr]₁
        [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [G] Wk.id ⊢Γ [fstp])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [fstp])
        [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [fstp]) ([G]₁ Wk.id ⊢Γ₁ [fstp]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            [fstp] [fstr] [fst≡] [snd≡]
  convEqTermT₂ {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) t≡u = {!!}
  convEqTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) A≡B t≡u = {!!}
  convEqTermT₂ (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) A≡B t≡u = {!!}

  -- Conversion of term equality converting from left to right.
  convEqTerm₁ : ∀ {k k′ A B t u} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
              → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
              → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
              → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from right to left.
  convEqTerm₂ : ∀ {k k′ A B t u} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
            → Γ / lε ⊩⟨ k ⟩  A ≡ B / [A]
            → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
            → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u


