{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Escape {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l

escapeAux : ∀ {k A B} ([B] :  Γ / lε ⊩⟨ k ⟩ B) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ A
escapeAux (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite redU* D' = Uᵣ′ k′ k< ⊢Γ
escapeAux (ℕᵣ [ ⊢B , ⊢ℕ , D ]) [ ⊢A , ⊢B' , D' ] = ℕᵣ ([ ⊢A , ⊢ℕ , ⇒*-comp D' D ])
escapeAux (Emptyᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = Emptyᵣ ([ ⊢A , ⊢Empty , ⇒*-comp D' D ])
escapeAux (Unitᵣ [ ⊢B , ⊢Unit , D ]) [ ⊢A , ⊢B' , D' ] = Unitᵣ ([ ⊢A , ⊢Unit , ⇒*-comp D' D ])
escapeAux (ne (ne K [ ⊢B , ⊢K , D ] neK K≡K)) [ ⊢A , ⊢B' , D' ] = ne (ne K ([ ⊢A , ⊢K , ⇒*-comp D' D ]) neK K≡K)
escapeAux (Bᵣ W (Bᵣ F G [ ⊢B , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) ([ ⊢A , ⊢B' , D' ]) =
  Bᵣ W (Bᵣ F G ([ ⊢A , ⊢Π , ⇒*-comp D' D ]) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
escapeAux (emb {l} {lε} {A}  0<1 [A]) D = emb 0<1 (escapeAux [A] D)  
escapeAux (ϝᵣ [ ⊢B , ⊢C , D ] αB  tB fB) [ ⊢A , ⊢B' , D' ] = ϝᵣ ([ ⊢A , ⊢C , ⇒*-comp D' D ]) αB tB fB 


-- Reducible types are well-formed.
escape : ∀ {k A} → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊢ A
escape (Uᵣ′ k′ k< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (ϝᵣ [ ⊢A , ⊢B , D ] αB  tB fB) = ⊢A -- ϝⱼ (escape (escapeAux {!!} {!!})) (escape {!!})
escape (emb 0<1 A) = escape A
      
-- Reducible type equality respect the equality relation.


-- escapeEq : ∀ {k A B} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
--             → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
--             → Γ / lε ⊢ A ≅ B
-- escapeEq (Uᵣ′ k′ k< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
-- escapeEq {k = k} (ℕᵣ D) A=B  = LogRel.escapeEqℕ k (logRelRec _) D A=B
-- escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
-- escapeEq (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
-- escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
--   ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
-- escapeEq {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--              A=B = LogRel.escapeEqB k (logRelRec _) (Bᵣ _ _ D ⊢F ⊢G A≡A [F] [G] G-ext) A=B
--   -- ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
-- escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B
-- escapeEq (ϝᵣ [ ⊢A , ⊢B , D ] αB  tB fB) ( x , y ) = ≅-trans (≅-red D (id ⊢B) (αₙ αB) (αₙ αB) (≅-ϝ {!!} {!!})) (≅-ϝ (escapeEq tB x) (escapeEq fB y)) -- ≅-ϝ (escapeEq {!!} x) (escapeEq {!!} y)

-- -- Reducible terms are well-formed.
-- escapeTerm : ∀ {k A t} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
--               → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
--               → Γ / lε ⊢ t ∷ A
-- escapeTerm (Uᵣ′ k′ k< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
-- escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (Unitᵣ D) (Unitₜ e [ ⊢t , ⊢u , d ] prop) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                (Πₜ f [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                (Σₜ p [ ⊢t , ⊢u , d ] pProd p≅p [fst] [snd]) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (ϝᵣ A⇒B αB  tB fB) ( x , y ) = conv (ϝⱼ (escapeTerm tB x) (escapeTerm fB y)) (sym (subset* (red A⇒B))) --  ϝⱼ (escapeTerm {!!} x) (escapeTerm {!!} y)
-- escapeTerm (emb 0<1 A) t = escapeTerm A t

-- -- Reducible term equality respect the equality relation.
-- escapeTermEq : ∀ {k A t u} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
--                 → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A]
--                 → Γ / lε ⊢ t ≅ u ∷ A
-- escapeTermEq (Uᵣ′ k′ k< ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
--   ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
-- escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
--   let natK , natK′ = split prop
--   in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
--              (naturalWhnf natK) (naturalWhnf natK′) k≡k′
-- escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
--   let natK , natK′ = esplit prop
--   in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
--              (ne natK) (ne natK′) k≡k′
-- escapeTermEq {k} {Γ} {A} {t} {u} (Unitᵣ D) (Unitₜ₌ ⊢t ⊢u) =
--   let t≅u = ≅ₜ-η-unit ⊢t ⊢u
--       A≡Unit = subset* (red D)
--   in  ≅-conv t≅u (sym A≡Unit)
-- escapeTermEq (ne′ K D neK K≡K)
--                  (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
--   ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
--          (~-to-≅ₜ t≡u)
-- escapeTermEq (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                  (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
--   ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
-- escapeTermEq (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                  (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
--   ≅ₜ-red (red D) (redₜ d) (redₜ d′) Σₙ (productWhnf pProd) (productWhnf rProd) p≅r
-- escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u 
-- escapeTermEq (ϝᵣ A⇒B αB  tB fB) ( x , y ) = ≅-conv (≅ₜ-ϝ (escapeTermEq tB x) (escapeTermEq fB y)) (sym (subset* (red A⇒B)))
