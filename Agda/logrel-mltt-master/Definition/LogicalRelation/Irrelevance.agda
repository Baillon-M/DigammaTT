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
                         → Γ / lε ⊩⟨ k ⟩ t ∷ A / p
                         → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (𝔹ᵥ D D′) t = t
--   irrelevanceTermT (Emptyᵥ D D′) t eq₁ eq₂ eq₃ = t
--   irrelevanceTermT (Unitᵥ D D′) t eq₁ eq₂ eq₃ = t
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                   (Πₜ ⊢f f≡f N [f] N₁ [f]₁) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
        Nmax = max (max N N₁) [Fₙ]
    in  Πₜ (PE.subst (λ x → Γ / lε ⊢ t ∷ x) ΠFG≡ΠF₁G₁ ⊢f) (PE.subst (λ x → Γ / lε ⊢ t ≅ t ∷ x) ΠFG≡ΠF₁G₁ f≡f)
          Nmax (λ {_} {ρ} {Δ} {a} {b} [ρ] {l'} ≤ε lε' N<s N<s' ⊢Δ [a]₁ [b]₁ a≡b₁ →
                  let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                             ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) [a]₁
                      [b] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                             ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) [b]₁
                      a≡b = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                               ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) a≡b₁
                      (M , [Ga]) = ([G] [ρ] ≤ε lε' (≤-trans (MaxLess-r (max N N₁) [Fₙ]) N<s') ⊢Δ [a])
                      (K , fa≡fb) = [f] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') (≤-trans (≤-trans (MaxLess-l N N₁) (MaxLess-l _ _)) N<s') ⊢Δ [a] [b] a≡b
                      Kmax = max K M
                  in Kmax , λ ≤ε' lε'' M<s K<s →
                                  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                                     ([Ga] ≤ε' lε'' (≤-trans (MaxLess-r K M) K<s))
                                                     (proj₂ ([G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]₁) ≤ε' lε'' M<s)
                                                     (fa≡fb ≤ε' lε'' (≤-trans (MaxLess-r K M) K<s) (≤-trans (MaxLess-l K M) K<s)))
          Nmax (λ {_} {ρ} {Δ} {a} [ρ] {l'} ≤ε lε' N<s N<s' ⊢Δ [a]₁ →
                  let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                             ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) [a]₁
                      (M , [Ga]) = ([G] [ρ] ≤ε lε' (≤-trans (MaxLess-r (max N N₁) [Fₙ]) N<s') ⊢Δ [a])
                      (K , [fa]) = [f]₁ [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') (≤-trans (≤-trans (MaxLess-r N N₁) (MaxLess-l _ _)) N<s') ⊢Δ [a]
                      Kmax = max K M
                  in Kmax , λ ≤ε' lε'' M<s K<s →
                                  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                                   ([Ga] ≤ε' lε'' (≤-trans (MaxLess-r K M) K<s))
                                                   (proj₂ ([G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]₁) ≤ε' lε'' M<s)
                                                   ([fa] ≤ε' lε'' (≤-trans (MaxLess-r K M) K<s) (≤-trans (MaxLess-l K M) K<s)))
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                   (Σₜ p d pProd p≅p N [prop]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        Nmax = max N [Fₙ]
    in
    Σₜ p (PE.subst (λ x → Γ / lε ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d) pProd
         (PE.subst (λ x → Γ / lε ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p)
         Nmax
      λ ≤ε lε' N<s N<s' →
        let ([fst] , K , [snd]) = [prop] ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (≤-trans (MaxLess-l _ _) N<s')
            [fst]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                      ([F] Wk.id ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (Con≤ ≤ε (wf ⊢F)))
                                      ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) [fst]
            M , [Gfst] = [G] Wk.id ≤ε lε' (≤-trans (MaxLess-r N [Fₙ]) N<s') (Con≤ ≤ε (wf ⊢F)) [fst]
            M′ , [Gfst]′ = [G]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁)) [fst]′
            Kmax = max K M
        in [fst]′ , Kmax ,
          λ ≤ε' lε'' M<s K<s →
            let [[snd]] = [snd] ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s) (≤-trans (MaxLess-l _ _) K<s)
            in irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
                                ([Gfst] ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s))
                                ([Gfst]′ ≤ε' lε'' M<s) [[snd]]
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t



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
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) ne=
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                     (Πₜ₌ f≡g [f] [g] N [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΠ ΠFG≡ΠF₁G₁
        [A]         = Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [A]₁        = Bᵣ′ BΠ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        Nmax = max N [Fₙ]
    in  Πₜ₌ (PE.subst (λ x → Γ / lε ⊢ t ≅ u ∷ x) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            Nmax λ {_} {ρ} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) [a]₁
                  (M , [Ga]) = ([G] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ [a])
                  (K , fa≡ga) = [f≡g] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]
                  Kmax = max K M
              in Kmax , λ ≤ε' lε'' M<s K<s →
                          irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                             ([Ga] ≤ε' lε'' (≤-trans (MaxLess-r K M) K<s))
                                             (proj₂ ([G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]₁) ≤ε' lε'' M<s)
                                             (fa≡ga ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s) (≤-trans (MaxLess-l _ _) K<s)) 
  irrelevanceEqTermT {Γ = Γ} {lε = lε} {t = t} {u = u}
                     (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                     (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] N [prop]) =
    let ΣFG≡ΣF₁G₁   = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ = B-PE-injectivity BΣ ΣFG≡ΣF₁G₁
        [A]         = Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext
        [A]₁        = Bᵣ′ BΣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁
        Nmax = max N [Fₙ]
    in  Σₜ₌ p r (PE.subst (λ x → Γ / lε ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
                (PE.subst (λ x → Γ / lε ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
                (PE.subst (λ x → Γ / lε ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
                (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
                Nmax
                λ ≤ε lε' N<s N<s' →
                  let ([fstp] , [fstr] , [fst≡] , K , [snd]) =
                                [prop] ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (≤-trans (MaxLess-l _ _) N<s')
                      [fstp]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                                 ([F] Wk.id ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (Con≤ ≤ε (wf ⊢F)))
                                                 ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) [fstp]
                      [fstr]′ = irrelevanceTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                                 ([F] Wk.id ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (Con≤ ≤ε (wf ⊢F)))
                                                 ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) [fstr]
                      [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk Wk.id) F≡F₁)
                                                 ([F] Wk.id ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (Con≤ ≤ε (wf ⊢F)))
                                                 ([F]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁))) [fst≡]
                      M , [Gfst] = [G] Wk.id ≤ε lε' (≤-trans (MaxLess-r N [Fₙ]) N<s') (Con≤ ≤ε (wf ⊢F)) [fstp]
                      M′ , [Gfst]′ = [G]₁ Wk.id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F₁)) [fstp]′
                      Kmax = max K M
                  in [fstp]′ , [fstr]′ , [fst≡]′ , Kmax ,
                     λ ≤ε' lε'' M<s K<s →
                       let [[snd]] = [snd] ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s) (≤-trans (MaxLess-l _ _) K<s)
                       in irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
                                             ([Gfst] ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s))
                                             ([Gfst]′ ≤ε' lε'' M<s) [[snd]] 
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
  

  -- Irrelevance for type equality with propositionally equal second types
irrelevanceEqR′ : ∀ {A B B′ k} (eqB : B PE.≡ B′) (p : Γ / lε ⊩⟨ k ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ A ≡ B / p → Γ / lε ⊩⟨ k ⟩ A ≡ B′ / p
irrelevanceEqR′ PE.refl p A≡B = A≡B

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
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 with whrDet* (red D , ne neK) (red D₁ , ne neK₁)
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 | PE.refl = 
                 (ne₌ M D′ neM K≡M)
  irrelevanceEqT {Γ = Γ} {lε = lε} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                                       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
                                       (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′]) =
                 let ΠFG≡ΠF₁G₁   = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W ⟧ₙ)
                     F≡F₁ , G≡G₁ = B-PE-injectivity W ΠFG≡ΠF₁G₁
                     Nmax = max [F≡Fₙ] [Fₙ]
    in  B₌ F′ G′ D′ (PE.subst (λ x → Γ / lε ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B) Nmax
        (λ {m} {ρ} {Δ} [ρ] ≤ε lε' N<s N<s' ⊢Δ →
          let [F≡F′]₁ = [F≡F′] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (≤-trans (MaxLess-l _ _) N<s') ⊢Δ
          in irrelevanceEq′ (PE.cong (wk ρ) F≡F₁)
                            ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r [F≡Fₙ] [Fₙ]) N<s') ⊢Δ)
                            ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) [F≡F′]₁)
        λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ) [a]₁
                  (M , [Ga]) = [G] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ [Fₙ]) N<s') ⊢Δ [a]
                  (M' , [Ga']) = [G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]₁ 
                  (K , Ga≡Ga') = [G≡G′] [ρ] ≤ε lε' (≤-trans (MaxLess-r _ _) N<s') (≤-trans (MaxLess-l _ _) N<s') ⊢Δ [a]
                  Kmax = max K M
              in Kmax , λ ≤ε' lε'' M<s K<s →
                          irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                                         ([Ga] ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s))
                                         ([Ga'] ≤ε' lε'' M<s)
                                         (Ga≡Ga' ≤ε' lε'' (≤-trans (MaxLess-r _ _) K<s) (≤-trans (MaxLess-l _ _) K<s))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
  irrelevanceEqT {p = emb 0<1 p} {q = q} AB A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B



irrelevanceTermʷ : ∀ {A t k k′} (p : Γ / lε ⊩⟨ k ⟩ʷ A) (q : Γ / lε ⊩⟨ k′ ⟩ʷ A)
                → Γ / lε ⊩⟨ k ⟩ʷ t ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ʷ t ∷ A / q
irrelevanceTermʷ (N , p) (M , q) (L , t) =
  max N L , λ ≤ε lε' M<s L<s →
              irrelevanceTerm (p ≤ε lε' (≤-trans (MaxLess-l _ _) L<s))
                              (q ≤ε lε' M<s)
                              (t ≤ε lε' (≤-trans (MaxLess-l _ _) L<s) (≤-trans (MaxLess-r _ _) L<s))

irrelevanceEqTermʷ : ∀ {A t u k k′} (p : Γ / lε ⊩⟨ k ⟩ʷ A) (q : Γ / lε ⊩⟨ k′ ⟩ʷ A)
                  → Γ / lε ⊩⟨ k ⟩ʷ t ≡ u ∷ A / p → Γ / lε ⊩⟨ k′ ⟩ʷ t ≡ u ∷ A / q
irrelevanceEqTermʷ (N , p) (M , q) (L , t≡u) =
  max N L , λ ≤ε lε' M<s L<s →
              irrelevanceEqTerm (p ≤ε lε' (≤-trans (MaxLess-l _ _) L<s))
                                (q ≤ε lε' M<s)
                                (t≡u ≤ε lε' (≤-trans (MaxLess-l _ _) L<s) (≤-trans (MaxLess-r _ _) L<s))

irrelevanceEqʷ : ∀ {A B k k′} (p : Γ / lε ⊩⟨ k ⟩ʷ A) (q : Γ / lε ⊩⟨ k′ ⟩ʷ A)
                  → Γ / lε ⊩⟨ k ⟩ʷ A ≡ B / p → Γ / lε ⊩⟨ k′ ⟩ʷ A ≡ B / q
irrelevanceEqʷ (N , p) (M , q) (L , A≡B) =
  max N L , λ ≤ε lε' M<s L<s →
              irrelevanceEq (p ≤ε lε' (≤-trans (MaxLess-l _ _) L<s))
                            (q ≤ε lε' M<s)
                            (A≡B ≤ε lε' (≤-trans (MaxLess-l _ _) L<s) (≤-trans (MaxLess-r _ _) L<s))
                                
