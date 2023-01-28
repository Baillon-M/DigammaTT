{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped using (LCon ; ⊢ₗ_ ; Con ; Term ; 𝔹 ; ℕ)
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Wk
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Escape

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l

-- Weak head expansion of reducible types.
redSubst* : ∀ {A B k}
          → Γ / lε ⊢ A ⇒* B
          → Γ / lε ⊩⟨ k ⟩ B
          → ∃ λ ([A] : Γ / lε ⊩⟨ k ⟩ A)
          → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
redSubst* D (Uᵣ′ l′ l< ⊢Γ) rewrite redU* D =
  Uᵣ′ l′ l< ⊢Γ , ⊩¹≡U (Uᵣ l′ l< ⊢Γ) PE.refl
redSubst* D (ℕᵣ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , ⊩¹≡ℕ _ D′
redSubst* D (𝔹ᵣ [ ⊢B , ⊢𝔹 , D′ ]) =
  let ⊢A = redFirst* D
  in  𝔹ᵣ ([ ⊢A , ⊢𝔹 , D ⇨* D′ ]) , ⊩¹≡𝔹 _ D′
-- redSubst* D (Emptyᵣ [ ⊢B , ⊢Empty , D′ ]) =
--  let ⊢A = redFirst* D
--  in  Emptyᵣ ([ ⊢A , ⊢Empty , D ⇨* D′ ]) , D′
--redSubst* D (Unitᵣ [ ⊢B , ⊢Unit , D′ ]) =
--  let ⊢A = redFirst* D
--  in  Unitᵣ ([ ⊢A , ⊢Unit , D ⇨* D′ ]) , D′
redSubst* D (ne′ K [ ⊢B , ⊢K , D′ ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ K [ ⊢A , ⊢K , D ⇨* D′ ] neK K≡K)
  ,   ⊩¹≡ne _ (ne₌ _ [ ⊢B , ⊢K , D′ ] neK K≡K)
redSubst* D (Bᵣ′ W F G [ ⊢B , ⊢ΠFG , D′ ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Bᵣ′ W F G [ ⊢A , ⊢ΠFG , D ⇨* D′ ] ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {_} {_} {≤ε}) [G] G-ext)
  ,   ⊩¹≡B W _ (B₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ)) λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , ⊩¹≡emb _ _ y₁
redSubst* D (ϝᵣ mε B⇒B' αB' tB fB) =
  let tA , tA≡B = redSubst* (τRed* D) tB
      fA , fA≡B = redSubst* (τRed* D) fB
      D' = :⇒:*-comp [ redFirst* D , ⊢A-red B⇒B' , D ] B⇒B'
    in
    (ϝᵣ mε D' αB' tA fA , ⊩¹≡ϝ-l D' αB' tA fA tA≡B fA≡B)

-- Weak head expansion of reducible terms.
redSubst*Termℕ : ∀ {t u}
              → Γ / lε ⊢ t ⇒* u ∷ ℕ
              → Γ / lε ⊩ℕ u ∷ℕ
              → (Γ / lε ⊩ℕ t ∷ℕ)
                × Γ / lε ⊩ℕ t ≡ u ∷ℕ
redSubst*Termℕ t⇒u (ℕₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let ⊢t   = redFirst*Term t⇒u
  in
  ℕₜ n [ ⊢t , ⊢n , t⇒u ⇨∷* d ] n≡n prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflNatural-prop prop)
redSubst*Termℕ t⇒u (ℕϝ tu fu) =
  let tt , tt≡u = redSubst*Termℕ (τRed*Term t⇒u) tu
      ft , ft≡u = redSubst*Termℕ (τRed*Term t⇒u) fu
  in ℕϝ tt ft , ℕ₌ϝ tt≡u ft≡u


redSubst*Term𝔹 : ∀ {t u}
              → Γ / lε ⊢ t ⇒* u ∷ 𝔹
              → Γ / lε ⊩𝔹 u ∷𝔹
              → (Γ / lε ⊩𝔹 t ∷𝔹)
                × Γ / lε ⊩𝔹 t ≡ u ∷𝔹
redSubst*Term𝔹 t⇒u (𝔹ₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let ⊢t   = redFirst*Term t⇒u
  in
  𝔹ₜ n [ ⊢t , ⊢n , t⇒u ⇨∷* d ] n≡n prop
  ,   𝔹ₜ₌ n n [ ⊢t , ⊢n , t⇒u ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflBoolean-prop prop)
redSubst*Term𝔹 t⇒u (𝔹ϝ tu fu) =
  let tt , tt≡u = redSubst*Term𝔹 (τRed*Term t⇒u) tu
      ft , ft≡u = redSubst*Term𝔹 (τRed*Term t⇒u) fu
  in 𝔹ϝ tt ft , 𝔹₌ϝ tt≡u ft≡u


redSubst*TermNe : ∀ {A t u} (neA : Γ / lε ⊩ne A)
              → Γ / lε ⊢ t ⇒* u ∷ A
              → Γ / lε ⊩ne u ∷ A / neA
              → (Γ / lε ⊩ne t ∷ A / neA)
                × (Γ / lε ⊩ne t ≡ u ∷ A / neA)
redSubst*TermNe (ne K D neK K≡K) t⇒u (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*TermNe (ne K D neK K≡K) t⇒u (neϝ tu fu) = 
  let tt , tt≡u = redSubst*TermNe _ (τRed*Term t⇒u) tu
      ft , ft≡u = redSubst*TermNe _ (τRed*Term t⇒u) fu
  in neϝ tt ft , ne₌ϝ tt≡u ft≡u

redSubst*Term : ∀ {A t u k}
              → Γ / lε ⊢ t ⇒* u ∷ A
              → ([A] : Γ / lε ⊩⟨ k ⟩ A)
              → Γ / lε ⊩⟨ k ⟩ u ∷ A / [A]
              → (Γ / lε ⊩⟨ k ⟩ t ∷ A / [A])
              × (Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A])
redSubst*Term t⇒u (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA A≡A [u]))
  in Uₜ A [d′] typeA A≡A (proj₁ q)
  ,  Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
redSubst*Term t⇒u (ℕᵣ D) ⊢u =
  let A≡ℕ  = subset* (red D)
      t⇒u′ = conv* t⇒u A≡ℕ
  in redSubst*Termℕ t⇒u′ ⊢u
redSubst*Term t⇒u (𝔹ᵣ D) ⊢u =
  let A≡ℕ  = subset* (red D)
      t⇒u′ = conv* t⇒u A≡ℕ
  in redSubst*Term𝔹 t⇒u′ ⊢u
--redSubst*Term t⇒u (Emptyᵣ D) (Emptyₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
--  let A≡Empty  = subset* (red D)
--      ⊢t   = conv (redFirst*Term t⇒u) A≡Empty
--      t⇒u′ = conv* t⇒u A≡Empty
--  in  Emptyₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
--  ,   Emptyₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
--          n≡n (reflEmpty-prop prop)
--redSubst*Term t⇒u (Unitᵣ D) (Unitₜ n [ ⊢u , ⊢n , d ] prop) =
--  let A≡Unit  = subset* (red D)
--      ⊢t   = conv (redFirst*Term t⇒u) A≡Unit
--      t⇒u′ = conv* t⇒u A≡Unit
--  in  Unitₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] prop
--  ,   Unitₜ₌ ⊢t ⊢u
redSubst*Term t⇒u (ne neA) net = redSubst*TermNe neA t⇒u net
redSubst*Term {Γ = Γ} {A = A} {t = t} {u = u} {k = k} t⇒u [A]@(Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  [u]@(Πₜ ⊢f f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [u′] = Πₜ (redFirst*Term t⇒u′)
                (≅ₜ-red₂ (id (⊢B-red D)) t⇒u′ t⇒u′ f≡f)
                         (λ {_} {_} {_} {_} {_} {_} {≤ε} [ρ] ⊢Δ [a] [b] [a≡b]
                           → let ua≡ub = [f] [ρ] ⊢Δ [a] [b] [a≡b]
                                 ⊢ta , ta≡ua = redSubst*Term {k = k} (app-subst* (Wk.wkRed*Term [ρ] ⊢Δ (RedTerm≤* ≤ε t⇒u′)) (escapeTerm ([F] [ρ] ⊢Δ) [a])) ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a])
                             in {!!}) {!!} --[f] [f]₁
  in  [u′]
  ,   Πₜ₌ {!!} [u′] [u]
          (λ [ρ] ⊢Δ [a] → {!!}) -- reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))
redSubst*Term {Γ = Γ} {A = A} {t = t} {u = u} {k = k} t⇒u (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  [u]@(Σₜ p [d]@([ ⊢t , ⊢u , d ]) pProd p≅p [fst] [snd]) =
  let A≡ΣFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΣFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΣFG , ⊢u , conv* t⇒u A≡ΣFG ⇨∷* d ]
      [u′] = Σₜ p [d′] pProd p≅p [fst] [snd]
  in  [u′]
  ,   Σₜ₌ p p [d′] [d] pProd pProd p≅p [u′] [u] [fst] [fst]
          (reflEqTerm ([F] Wk.id (wf ⊢F)) [fst])
          (reflEqTerm ([G] Wk.id (wf ⊢F) [fst]) [snd])
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]
redSubst*Term t⇒u (ϝᵣ mε A⇒B αB tA fA) (tu , fu) =
  let tt , tt≡u = redSubst*Term (τRed*Term t⇒u) tA tu
      ft , ft≡u = redSubst*Term (τRed*Term t⇒u) fA fu
  in (tt , ft) , (tt≡u , ft≡u)

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B k}
         → Γ / lε ⊢ A ⇒ B
         → Γ / lε ⊩⟨ k ⟩ B
         → ∃ λ ([A] : Γ / lε ⊩⟨ k ⟩ A)
         → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u k}
             → Γ / lε ⊢ t ⇒ u ∷ A
             → ([A] : Γ / lε ⊩⟨ k ⟩ A)
             → Γ / lε ⊩⟨ k ⟩ u ∷ A / [A]
             → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
             × Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]
