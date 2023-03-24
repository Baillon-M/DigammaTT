{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l

mutual
  -- Helper function for symmetry of type equality using shape views.
  symEqT : ∀ {A B k k′} {[A] : Γ / lε ⊩⟨ k ⟩ A} {[B] : Γ / lε ⊩⟨ k′ ⟩ B}
         → ShapeView Γ k k′ A B [A] [B]
         → Γ / lε ⊩⟨ k  ⟩ A ≡ B / [A]
         → Γ / lε ⊩⟨ k′ ⟩ B ≡ A / [B]
  symEqT (ℕᵥ D D′) A≡B = red D
  symEqT (𝔹ᵥ D D′) A≡B = red D
--  symEqT (Emptyᵥ D D′) A≡B = red D
--  symEqT (Unitᵥ D D′) A≡B = red D
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
         rewrite whrDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK
        (~-sym K≡M)
  symEqT {Γ = Γ} (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [Fₙ] [F] [G] G-ext)
                       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [Fₙ]₁ [F]₁ [G]₁ G-ext₁))
         (B₌ F′ G′ D′ A≡B [F≡Fₙ] [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , ⟦ W ⟧ₙ) (D′ , ⟦ W ⟧ₙ)
        F₁≡F′ , G₁≡G′ = B-PE-injectivity W ΠF₁G₁≡ΠF′G′
    in B₌ _ _ (red D)
         (≅-sym
          (PE.subst (λ x → Γ / _ ⊢ ⟦ W ⟧ F ▹ G ≅ x) (PE.sym ΠF₁G₁≡ΠF′G′)
           A≡B))
         (max [Fₙ] [F≡Fₙ])
         (λ {m} {ρ} {Δ} [ρ] ≤ε lε' N<s N<s' ⊢Δ →
           let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
               [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ / _ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ)
           in irrelevanceEq′ {Γ = Δ} (ρF′≡ρF₁ ρ)
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ)
                             (symEq ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-l _ _) N<s') ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                             ([F≡F′] [ρ] ≤ε lε' (≤-trans (MaxLess-l _ _) N<s') (≤-trans (MaxLess-r _ _) N<s') ⊢Δ)))
           λ {m ρ Δ} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a]₁ →
             let Fₙ<s = ≤-trans (MaxLess-l _ _) N<s'
                 F≡Fₙ<s = ≤-trans (MaxLess-r _ _) N<s'
                 ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
                 [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ / _ ⊩⟨ _ ⟩ wk ρ x) F₁≡F′ ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ)
                 [F₁≡F] = irrelevanceEq′ {Γ = Δ} (ρF′≡ρF₁ ρ)
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ)
                             (symEq ([F] [ρ] ≤ε lε' (≤-trans (MaxLess-l _ _) N<s') ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                             ([F≡F′] [ρ] ≤ε lε' (≤-trans (MaxLess-l _ _) N<s') (≤-trans (MaxLess-r _ _) N<s') ⊢Δ))
                 ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                 [a] = convTerm₁ ([F]₁ [ρ] ≤ε lε' N<s ⊢Δ) ([F] [ρ] ≤ε lε' Fₙ<s ⊢Δ) [F₁≡F] [a]₁
                 (M , [Ga]) = ([G] [ρ] ≤ε lε' Fₙ<s ⊢Δ [a])
                 (M' , [Ga]') = ([G]₁ [ρ] ≤ε lε' N<s ⊢Δ [a]₁)
                 (M'' , [G≡Ga]) = [G≡G′] [ρ] ≤ε lε' Fₙ<s F≡Fₙ<s ⊢Δ [a]
                 Kmax = max M M''
             in Kmax , λ ≤ε' lε'' M<s K<s →
                let M<s' = ≤-trans (MaxLess-l M M'') K<s
                    M<s'' = ≤-trans (MaxLess-r M M'') K<s
                    [ρG′a] = PE.subst (λ x → _ / _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ]) G₁≡G′
                                      ([Ga]' ≤ε' lε'' M<s)
                in irrelevanceEq′ ρG′a≡ρG₁′a [ρG′a] ([Ga]' ≤ε' lε'' M<s) (symEq ([Ga] ≤ε' lε'' M<s') [ρG′a] ([G≡Ga] ≤ε' lε'' M<s' M<s''))
  symEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  -- Symmetry of type equality.
  symEq : ∀ {A B k k′} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
        → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
        → Γ / lε ⊩⟨ k′ ⟩ B ≡ A / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

symNeutralTerm : ∀ {t u A}
               → Γ / lε ⊩neNf t ≡ u ∷ A
               → Γ / lε ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symNatural-prop : ∀ {k k′}
                → [Natural]-prop Γ lε k k′
                → [Natural]-prop Γ lε k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symBoolean-prop : ∀ {k k′}
                → [Boolean]-prop Γ lε k k′
                → [Boolean]-prop Γ lε k′ k
symBoolean-prop trueᵣ = trueᵣ
symBoolean-prop falseᵣ = falseᵣ
symBoolean-prop (ne prop) = ne (symNeutralTerm prop)

-- symEmpty-prop : ∀ {k k′}
--               → [Empty]-prop Γ k k′
--               → [Empty]-prop Γ k′ k
-- symEmpty-prop (ne prop) = ne (symNeutralTerm prop)

-- Symmetry of term equality.
symEqTerm : ∀ {k A t u} ([A] : Γ / lε ⊩⟨ k ⟩ A)
          → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A]
          → Γ / lε ⊩⟨ k ⟩ u ≡ t ∷ A / [A]
symEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm (𝔹ᵣ D) (𝔹ₜ₌ k k′ d d′ t≡u prop) =
  𝔹ₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symBoolean-prop prop) --(symNatural-prop prop)
-- symEqTerm (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ t≡u prop) =
--   Emptyₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symEmpty-prop prop)
-- symEqTerm (Unitᵣ D) (Unitₜ₌ ⊢t ⊢u) =
--   Unitₜ₌ ⊢u ⊢t
symEqTerm (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F]ₙ [F] [G] G-ext)
          (Πₜ₌ f≡g [f] [g] N [f≡g]) =
  Πₜ₌ (≅ₜ-sym f≡g) [g] [f] N
      (λ {m} {ρ} {Δ} {a} [ρ] ≤ε lε' N<s N<s' ⊢Δ [a] →
        let (M , [f≡ga]) = [f≡g] [ρ] ≤ε lε' N<s N<s' ⊢Δ [a]
            (M' , [Ga]) = [G] [ρ] ≤ε lε' N<s ⊢Δ [a]
        in M , (λ ≤ε' lε'' M<s M<s' → symEqTerm ([Ga] ≤ε' lε'' M<s) ([f≡ga] ≤ε' lε'' M<s M<s')))
symEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F]ₙ [F] [G] G-ext)
          (Σₜ₌  p r d d′ pProd rProd p≅r [t] [u] N [prop≡]) =
  let ⊢Γ = wf ⊢F
      -- [Gfstp≡Gfstr] = G-ext Wk.id ⊢Γ [fstp] [fstr] [fst≡]
  in  Σₜ₌ r p d′ d rProd pProd (≅ₜ-sym p≅r) [u] [t] N
          (λ ≤ε lε' N<s N<s' →
            let ([fstp] , [fstr] , [fst≡] , K , [snd≡]) = [prop≡] ≤ε lε' N<s N<s'
                M , [Gfstp] = [G] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ) [fstp]
                M' , [Gfstr] = [G] Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ) [fstr]
                [Gfstp≡Gfstr] = G-ext Wk.id ≤ε lε' N<s (Con≤ ≤ε ⊢Γ) [fstp] [fstr] [fst≡]
                Kmax = max M K
            in [fstr] , [fstp] , symEqTerm ([F] Wk.id ≤ε lε' N<s _) [fst≡] , Kmax ,
               λ ≤ε' lε'' M<s K<s →
                let M<s' = (≤-trans (MaxLess-l _ _) K<s)
                    K<s' = (≤-trans (MaxLess-r _ _) K<s)
                    [[Gfstp]] = ([Gfstp] ≤ε' lε'' M<s')
                    [[Gfstp≡Gfstr]] = [Gfstp≡Gfstr] ≤ε' lε'' M<s'
                in convEqTerm₁ [[Gfstp]] ([Gfstr] ≤ε' lε'' M<s) [[Gfstp≡Gfstr]]
                               (symEqTerm [[Gfstp]] ([snd≡] ≤ε' lε'' M<s' K<s')))
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
