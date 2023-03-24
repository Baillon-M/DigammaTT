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
open import Definition.LogicalRelation.Properties.Escape
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
             → (A≡B : Γ / lε ⊩⟨ k ⟩  A ≡ B / [A])
             → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
             → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (𝔹ᵥ D D′) A≡B t = t
  -- convTermT₁ (Emptyᵥ D D′) A≡B t = t
  -- convTermT₁ (Unitᵥ D D′) A≡B t = t
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k))
             with whrDet* (red D′ , ne neM) (red D₁ , ne neK₁)
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k))
             | PE.refl =
             neₜ k (convRed:*: d (≅-eq (~-to-≅ K≡M)))
               (neNfₜ neK₂ (conv ⊢k (≅-eq (~-to-≅ K≡M))) (~-conv k≡k (≅-eq (~-to-≅ K≡M))))
  convTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
             (Πₜ ⊢f f≡f N [f] N₁ [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
        Nmax = max N (max [F≡Fₙ] [Fₙ])
        Nmax₁ = max N₁ (max [F≡Fₙ] [Fₙ])
    in  Πₜ (conv ⊢f ΠFG≡ΠF₁G₁) (≅-conv f≡f ΠFG≡ΠF₁G₁) Nmax
           (λ {m} {ρ} {Δ} {a} {b} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] [b] a≡b →
              let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
                  F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
                  [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                           ([F≡F′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                   ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂ ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                   ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F₁] [b]
                  a≡b₁ = convEqTerm₂ ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                     ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F₁] a≡b
                  (M , [Ga]) = ([G] [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁)
                  (M′ , [Ga]′) = [G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]
                  (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ [a]₁
                  (K , [f≡fa]) = [f] [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁ [b]₁ a≡b₁
                  Kmax = max K (max M M'')
              in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s')
                                              ([G≡Ga] ≤ε' lε'' M<s' M<s'')
                 in convEqTerm₁ ([Ga] ≤ε' lε'' M<s')
                                ([Ga]′ ≤ε' lε'' M<s) [G≡G₁]
                                ([f≡fa] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
           Nmax₁
           (λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] →
              let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N₁ _)) N<s'
                  F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N₁ _)) N<s'
                  [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                           ([F≡F′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                           ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F₁] [a]
                  (M , [Ga]) = ([G] [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁)
                  (M′ , [Ga]′) = [G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]
                  (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ [a]₁
                  (K , [fa]) = [f]₁ [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁
                  Kmax = max K (max M M'')
              in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l M M'') (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s')
                                              ([G≡Ga] ≤ε' lε'' M<s' M<s'')
                 in convTerm₁ ([Ga] ≤ε' lε'' M<s') ([Ga]′ ≤ε' lε'' M<s) [G≡G₁]
                              ([fa] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
  convTermT₁ {Γ = Γ} {lε = lε} {k = k} {k′ = k′} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                                        (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
             (Σₜ p d pProd p≅p N [prop]) =
    let ΣF₁G₁≡ΣF′G′   = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
                             (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        Nmax = max N (max [F≡Fₙ] [Fₙ])
    in Σₜ p (convRed:*: d ΣFG≡ΣF₁G₁) pProd (≅-conv p≅p ΣFG≡ΣF₁G₁) Nmax
       λ ≤ε lε' N<s N<s' →
         let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
             F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
             F≡F₁ = PE.subst (λ x → Γ / lε' ⊩⟨ k ⟩ wk id F ≡ wk id x / [F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                             (PE.sym F₁≡F′)
                             ([F≡F′] Wk.id ≤ε lε' Fₙ<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ))
             ([fst] , K , [snd]) = [prop] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s')
             [fst]₁ = convTerm₁ ([F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                                ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fst]
             (M , [[G]]) = [G] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ) [fst]
             (M' , [[G]]₁) = [G]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁)) [fst]₁
             (M'' , [G≡Ga]) = [G≡G′] Wk.id ≤ε lε' Fₙ<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ) [fst]
             Kmax = max K (max M M'')
         in [fst]₁ , Kmax , λ ≤ε' lε'' M<s K<s →
           let M<s' = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r K _)) K<s
               M<s'' = ≤-trans (≤-trans (MaxLess-r _ _)(MaxLess-r K _)) K<s
               G≡G₁ = PE.subst (λ x → Γ / lε'' ⊩⟨ k ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [[G]] ≤ε' lε'' M<s')
                               (PE.sym G₁≡G′) ([G≡Ga] ≤ε' lε'' M<s' M<s'')
               [[snd]] = [snd] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)
           in convTerm₁ ([[G]] ≤ε' lε'' M<s') ([[G]]₁ ≤ε' lε'' M<s) G≡G₁ [[snd]]
  convTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t
  
  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {k k′ A B t} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
           → ShapeView Γ k k′ A B [A] [B]
           → (A≡B : Γ / lε ⊩⟨ k ⟩  A ≡ B / [A])
           → Γ / lε ⊩⟨ k′ ⟩ t ∷ B / [B]
           → Γ / lε ⊩⟨ k ⟩  t ∷ A / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (𝔹ᵥ D D′) A≡B t = t
  -- convTermT₂ (Emptyᵥ D D′) A≡B t = t
  -- convTermT₂ (Unitᵥ D D′) A≡B t = t
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _  / _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                      (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
             (Πₜ ⊢f f≡f N [f] N₁ [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
        Nmax = max N (max [F≡Fₙ] [Fₙ]₁)
        Nmax₁ = max N₁ (max [F≡Fₙ] [Fₙ]₁)
    in  Πₜ (conv ⊢f (sym ΠFG≡ΠF₁G₁)) (≅-conv f≡f (sym ΠFG≡ΠF₁G₁)) Nmax
           (λ {m} {ρ} {Δ} {a} {b} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] [b] a≡b →
              let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
                  F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
                  [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                           ([F≡F′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                   ([F]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁ ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                   ([F]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F≡F₁] [b]
                  a≡b₁ = convEqTerm₁ ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                     ([F]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F≡F₁] a≡b
                  (M , [Ga]) = ([G] [ρ] ≤ε lε' N<s ⊢Δ [a])
                  (M' , [Ga]') = [G]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁
                  (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ [a]
                  (K , [f≡fa]) = [f] [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁ [b]₁ a≡b₁
                  Kmax = max K (max M' M'')
              in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l M' M'') (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M' M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s)
                                              ([G≡Ga] ≤ε' lε'' M<s M<s'')
                 in convEqTerm₂ ([Ga] ≤ε' lε'' M<s)
                                ([Ga]' ≤ε' lε'' M<s') [G≡G₁]
                                ([f≡fa] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
           Nmax₁
           (λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] →
              let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N₁ _)) N<s'
                  F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N₁ _)) N<s'
                  [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                           ([F≡F′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                   ([F]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F≡F₁] [a]
                  (M , [Ga]) = ([G] [ρ] ≤ε lε' N<s ⊢Δ [a])
                  (M' , [Ga]') = [G]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁
                  (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ [a]
                  (K , [fa]) = [f]₁ [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁
                  Kmax = max K (max M' M'')
              in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l M' M'') (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M' M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s)
                                              ([G≡Ga] ≤ε' lε'' M<s M<s'')
                 in convTerm₂ ([Ga] ≤ε' lε'' M<s) ([Ga]' ≤ε' lε'' M<s') [G≡G₁]
                              ([fa] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
  convTermT₂ {Γ = Γ} {lε = lε} {k = k} {k′ = k′} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                                        (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
             (Σₜ p d pProd p≅p N [prop]) =
    let ΣF₁G₁≡ΣF′G′   = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        Nmax = max N (max [F≡Fₙ] [Fₙ]₁)
    in Σₜ p (convRed:*: d (sym ΣFG≡ΣF₁G₁)) pProd (≅-conv p≅p (sym ΣFG≡ΣF₁G₁)) Nmax
       λ ≤ε lε' N<s N<s' →
         let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
             F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
             F≡F₁ = PE.subst (λ x → Γ / lε' ⊩⟨ k ⟩ wk id F ≡ wk id x / [F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                             (PE.sym F₁≡F′)
                             ([F≡F′] Wk.id ≤ε lε' N<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ))
             ([fst] , K , [snd]) = [prop] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s')
             [fst]₁ = convTerm₂ ([F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                                ([F]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fst]
             (M , [[G]]) = [G] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ) [fst]₁
             (M' , [[G]]₁) = [G]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁)) [fst]
             (M'' , [G≡Ga]) = [G≡G′] Wk.id ≤ε lε' N<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ) [fst]₁
             Kmax = max K (max M' M'')
         in [fst]₁ , Kmax , λ ≤ε' lε'' M<s K<s →
           let M<s' = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r K _)) K<s
               M<s'' = ≤-trans (≤-trans (MaxLess-r _ _)(MaxLess-r K _)) K<s
               G≡G₁ = PE.subst (λ x → Γ / lε'' ⊩⟨ k ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [[G]] ≤ε' lε'' M<s)
                               (PE.sym G₁≡G′) ([G≡Ga] ≤ε' lε'' M<s M<s'')
               [[snd]] = [snd] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)
           in convTerm₂ ([[G]] ≤ε' lε'' M<s) ([[G]]₁ ≤ε' lε'' M<s') G≡G₁ [[snd]]
  convTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t
  
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
               → (A≡B : Γ / lε ⊩⟨ k ⟩  A ≡ B / [A])
               → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
               → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (𝔹ᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₁ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _  / _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                        [A≡B]@(B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
               (Πₜ₌ f≡g [f] [g] N [f≡g]) =
    let [A] = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [B] = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        Nmax = max N (max [F≡Fₙ] [Fₙ])
    in Πₜ₌ (≅-conv f≡g ΠFG≡ΠF₁G₁) (convTerm₁ [A] [B] [A≡B] [f]) (convTerm₁ [A] [B] [A≡B] [g])
           Nmax
           (λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] →
             let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
                 F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
                 [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                                          ([F≡F′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ)
                 [a]₁ = convTerm₂ ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ)
                        ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F₁] [a]
                 (M , [Ga]) = ([G] [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁)
                 (M′ , [Ga]′) = [G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]
                 (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ [a]₁
                 (K , [f≡ga]) = [f≡g] [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁
                 Kmax = max K (max M M'')
             in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l M M'') (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s')
                                              ([G≡Ga] ≤ε' lε'' M<s' M<s'')
                 in convEqTerm₁ ([Ga] ≤ε' lε'' M<s') ([Ga]′ ≤ε' lε'' M<s) [G≡G₁]
                              ([f≡ga] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
  convEqTermT₁ {Γ = Γ} {lε = lε} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                        [A≡B]@(B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
               (Σₜ₌  p r d d′ pProd rProd p≅r [t] [u] N [prop≡]) =
    let [A] = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [B] = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        ΣF₁G₁≡ΣF′G′ = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        Nmax = max N (max [F≡Fₙ] [Fₙ])
    in Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁) pProd rProd (≅-conv p≅r ΣFG≡ΣF₁G₁)
          (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
          Nmax
       λ ≤ε lε' N<s N<s' →
         let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
             F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
             F≡F₁ = PE.subst (λ x → Γ / lε' ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                             (PE.sym F₁≡F′)
                             ([F≡F′] Wk.id ≤ε lε' Fₙ<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ))
             ([fstp] , [fstr] , [fst≡] , K , [snd≡]) = [prop≡] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s')
             [fstp]₁ = convTerm₁ ([F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                                 ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fstp]
             [fstr]₁ = convTerm₁ ([F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                                 ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fstr]
             [fst≡]₁ = convEqTerm₁ ([F] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ))
                                   ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fst≡]
             (M , [[G]]) = [G] Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε ⊢Γ) [fstp]
             (M' , [[G]]₁) = [G]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁)) [fstp]₁
             (M'' , [G≡Ga]) = [G≡G′] Wk.id ≤ε lε' Fₙ<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ) [fstp]
             Kmax = max K (max M M'')
         in [fstp]₁ , [fstr]₁ , [fst≡]₁ , Kmax , λ ≤ε' lε'' M<s K<s →
           let M<s' = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r K _)) K<s
               M<s'' = ≤-trans (≤-trans (MaxLess-r _ _)(MaxLess-r K _)) K<s
               G≡G₁ = PE.subst (λ x → Γ / lε'' ⊩⟨ _ ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [[G]] ≤ε' lε'' M<s')
                               (PE.sym G₁≡G′) ([G≡Ga] ≤ε' lε'' M<s' M<s'')
               [[snd≡]] = [snd≡] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)
           in convEqTerm₁ ([[G]] ≤ε' lε'' M<s') ([[G]]₁ ≤ε' lε'' M<s) G≡G₁ [[snd≡]]
  convEqTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {k k′ A B t u} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
             → ShapeView Γ k k′ A B [A] [B]
             → (A≡B : Γ / lε ⊩⟨ k ⟩  A ≡ B / [A])
             → Γ / lε ⊩⟨ k′ ⟩ t ≡ u ∷ B / [B]
             → Γ / lε ⊩⟨ k ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (𝔹ᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  -- convEqTermT₂ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _  / _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                        [A≡B]@(B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
               (Πₜ₌ f≡g [f] [g] N [f≡g]) =
    let [A] = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [B] = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Π F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ ΠF₁G₁≡ΠF′G′
        Nmax = max N (max [F≡Fₙ] [Fₙ]₁)
    in Πₜ₌ (≅-conv f≡g (sym ΠFG≡ΠF₁G₁)) (convTerm₂ [A] [B] [A≡B] [f]) (convTerm₂ [A] [B] [A≡B] [g])
           Nmax
           (λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] →
             let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
                 F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
                 [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                                          ([F≡F′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ)
                 [a]₁ = convTerm₁ ([F] [ρ] ≤ε lε' N<s ⊢Δ)
                        ([F]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F≡F₁] [a]
                 (M , [Ga]) = ([G] [ρ] ≤ε lε' N<s ⊢Δ [a])
                 (M′ , [Ga]′) = [G]₁ [ρ] ≤ε lε' Fₙ<s ⊢Δ [a]₁
                 (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' N<s F≡Fₙ<s ⊢Δ [a]
                 (K , [f≡ga]) = [f≡g] [ρ] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]₁
                 Kmax = max K (max M′ M'')
             in Kmax , λ ≤ε' lε'' M<s K<s →
                 let M<s' = ≤-trans (≤-trans (MaxLess-l M′ M'') (MaxLess-r K _)) K<s
                     M<s'' = ≤-trans (≤-trans (MaxLess-r M′ M'')(MaxLess-r K _)) K<s
                     [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                              (PE.sym G₁≡G′)) ([Ga] ≤ε' lε'' M<s)
                                              ([G≡Ga] ≤ε' lε'' M<s M<s'')
                 in convEqTerm₂ ([Ga] ≤ε' lε'' M<s) ([Ga]′ ≤ε' lε'' M<s') [G≡G₁]
                              ([f≡ga] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)))
  --   Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
  --           funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
  --           (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
  --           (λ {_} {ρ} {Δ : Con Term _} {a} {l' : LCon} {≤ε : _ ≤ₗ l'} [ρ] ⊢Δ [a] →
  --              let F₁≡F′ , G₁≡G′ = B-PE-injectivity BΠ (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
  --                  [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
  --                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
  --                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ {≤ε = ≤ε} [ρ] ⊢Δ) [F≡F₁] [a]
  --                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
  --                                                    (PE.sym G₁≡G′))
  --                                           ([G] [ρ] ⊢Δ [a])
  --                                           ([G≡G′] [ρ] ⊢Δ [a])
  --              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
  --                              [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂ {Γ = Γ} {lε = lε} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                        (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                        [A≡B]@(B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′])
               (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] N [prop≡]) =
    let [A] = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [B] = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        ΣF₁G₁≡ΣF′G′ = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity BΣ ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ  / lε ⊢ Σ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        Nmax = max N (max [F≡Fₙ] [Fₙ]₁)
    in Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁)) pProd rProd (≅-conv p≅r (sym ΣFG≡ΣF₁G₁))
          (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
          Nmax
       λ ≤ε lε' N<s N<s' →
         let Fₙ<s = ≤-trans (≤-trans (MaxLess-r _ _) (MaxLess-r N _)) N<s'
             F≡Fₙ<s = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r N _)) N<s'
             F≡F₁ = PE.subst (λ x → Γ / lε' ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                             (PE.sym F₁≡F′)
                             ([F≡F′] Wk.id ≤ε lε' N<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ))
             ([fstp] , [fstr] , [fst≡] , K , [snd≡]) = [prop≡] ≤ε lε' Fₙ<s (≤-trans (MaxLess-l _ _) N<s')
             [fstp]₁ = convTerm₂ ([F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                                 ([F]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fstp]
             [fstr]₁ = convTerm₂ ([F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                                 ([F]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fstr]
             [fst≡]₁ = convEqTerm₂ ([F] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ))
                                   ([F]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁))) F≡F₁ [fst≡]
             (M , [[G]]) = [G] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ) [fstp]₁
             (M' , [[G]]₁) = [G]₁ Wk.id ≤ε lε' Fₙ<s (Con≤ ≤ε (wf ⊢F₁)) [fstp]
             (M'' , [G≡Ga]) = [G≡G′] Wk.id ≤ε lε' N<s F≡Fₙ<s (Con≤ ≤ε ⊢Γ) [fstp]₁
             Kmax = max K (max M' M'')
         in [fstp]₁ , [fstr]₁ , [fst≡]₁ , Kmax , λ ≤ε' lε'' M<s K<s →
           let M<s' = ≤-trans (≤-trans (MaxLess-l _ _) (MaxLess-r K _)) K<s
               M<s'' = ≤-trans (≤-trans (MaxLess-r _ _)(MaxLess-r K _)) K<s
               G≡G₁ = PE.subst (λ x → Γ / lε'' ⊩⟨ _ ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [[G]] ≤ε' lε'' M<s)
                               (PE.sym G₁≡G′) ([G≡Ga] ≤ε' lε'' M<s M<s'')
               [[snd≡]] = [snd≡] ≤ε' lε'' M<s' (≤-trans (MaxLess-l _ _) K<s)
           in convEqTerm₂ ([[G]] ≤ε' lε'' M<s) ([[G]]₁ ≤ε' lε'' M<s') G≡G₁ [[snd≡]]
     
  --       F≡F₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
  --                       (PE.sym F₁≡F′)
  --                       ([F≡F′] Wk.id ⊢Γ)
  --       [fstp] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstp]₁
  --       [fstr] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fstr]₁
  --       [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
  --       G≡G₁ = PE.subst (λ x → Γ / lε ⊩⟨ _ ⟩ wk (lift id) G [ fst p ] ≡ wk (lift id) x [ fst p ] / [G] Wk.id ⊢Γ [fstp])
  --                       (PE.sym G₁≡G′)
  --                       ([G≡G′] Wk.id ⊢Γ [fstp])
  --       [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [fstp]) ([G]₁ Wk.id ⊢Γ₁ [fstp]₁) G≡G₁ [snd≡]₁
  --   in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
  --           funcF funcG (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
  --           (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
  --           [fstp] [fstr] [fst≡] [snd≡]
  convEqTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u

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


-- Weak conversion of term equality converting from left to right.
convTerm₁ʷ : ∀ {k k′ A B t} ([A] : Γ / lε ⊩⟨ k ⟩ʷ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ʷ B)
            → Γ / lε ⊩⟨ k ⟩ʷ  A ≡ B / [A]
            → Γ / lε ⊩⟨ k ⟩ʷ  t ∷ A / [A]
            → Γ / lε ⊩⟨ k′ ⟩ʷ t ∷ B / [B]
convTerm₁ʷ (N , [A]) (M , [B]) (L , A≡B) (K , t) =
  max N (max L K) , λ ≤ε lε' M<s K<s →
    convTerm₁ ([A] ≤ε lε' (≤-trans (MaxLess-l _ _) K<s))
              ([B] ≤ε lε' M<s)
              (A≡B ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-l L K) (MaxLess-r N _)) K<s))
              (t ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-r L K) (MaxLess-r N _)) K<s))
                                                                       
-- Weak conversion of term equality converting from right to left.
convTerm₂ʷ : ∀ {k k′ A B t} ([A] : Γ / lε ⊩⟨ k ⟩ʷ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ʷ B)
             → Γ / lε ⊩⟨ k ⟩ʷ  A ≡ B / [A]
             → Γ / lε ⊩⟨ k′ ⟩ʷ t ∷ B / [B]
             → Γ / lε ⊩⟨ k ⟩ʷ  t ∷ A / [A]
convTerm₂ʷ (N , [A]) (M , [B]) (L , A≡B) (K , t) =
  max M (max L K) , λ ≤ε lε' N<s K<s →
    convTerm₂ ([A] ≤ε lε' N<s)
              ([B] ≤ε lε' (≤-trans (MaxLess-l _ _) K<s))
              (A≡B ≤ε lε' N<s (≤-trans (≤-trans (MaxLess-l L K) (MaxLess-r M _)) K<s))
              (t ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-r L K) (MaxLess-r M _)) K<s))


-- Weak conversion of term equality converting from left to right.
convEqTerm₁ʷ : ∀ {k k′ A B t u} ([A] : Γ / lε ⊩⟨ k ⟩ʷ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ʷ B)
            → Γ / lε ⊩⟨ k ⟩ʷ  A ≡ B / [A]
            → Γ / lε ⊩⟨ k ⟩ʷ  t ≡ u ∷ A / [A]
            → Γ / lε ⊩⟨ k′ ⟩ʷ t ≡ u ∷ B / [B]
convEqTerm₁ʷ (N , [A]) (M , [B]) (L , A≡B) (K , t≡u) =
  max N (max L K) , λ ≤ε lε' M<s K<s →
    convEqTerm₁ ([A] ≤ε lε' (≤-trans (MaxLess-l _ _) K<s))
                ([B] ≤ε lε' M<s)
                (A≡B ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-l L K) (MaxLess-r N _)) K<s))
                (t≡u ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-r L K) (MaxLess-r N _)) K<s))
                                                                       
-- Weak conversion of term equality converting from right to left.
convEqTerm₂ʷ : ∀ {k k′ A B t u} ([A] : Γ / lε ⊩⟨ k ⟩ʷ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ʷ B)
             → Γ / lε ⊩⟨ k ⟩ʷ  A ≡ B / [A]
             → Γ / lε ⊩⟨ k′ ⟩ʷ t ≡ u ∷ B / [B]
             → Γ / lε ⊩⟨ k ⟩ʷ  t ≡ u ∷ A / [A]
convEqTerm₂ʷ (N , [A]) (M , [B]) (L , A≡B) (K , t≡u) =
  max M (max L K) , λ ≤ε lε' N<s K<s →
    convEqTerm₂ ([A] ≤ε lε' N<s)
                ([B] ≤ε lε' (≤-trans (MaxLess-l _ _) K<s))
                (A≡B ≤ε lε' N<s (≤-trans (≤-trans (MaxLess-l L K) (MaxLess-r M _)) K<s))
                (t≡u ≤ε lε' (≤-trans (MaxLess-l _ _) K<s) (≤-trans (≤-trans (MaxLess-r L K) (MaxLess-r M _)) K<s))
