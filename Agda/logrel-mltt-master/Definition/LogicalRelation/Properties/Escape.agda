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
import Tools.Sum as TS
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
escapeAux (ϝᵣ mε [ ⊢B , ⊢C , D ] αB  tB fB) [ ⊢A , ⊢B' , D' ] = ϝᵣ mε ([ ⊢A , ⊢C , ⇒*-comp D' D ]) αB tB fB 


AntiRedLog : ∀ {k A B} ([B] :  Γ / lε ⊩⟨ k ⟩ A) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ B
AntiRedLog (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite PE.sym (whnfRed* D' Uₙ) = Uᵣ′ _ k< ⊢Γ -- Uᵣ′ k′ k< ⊢Γ
AntiRedLog (ℕᵣ [ ⊢A , ⊢ℕ , D ]) [ ⊢A' , ⊢B , D' ] = ℕᵣ ([ ⊢B , ⊢ℕ , whrDet↘ (D , ℕₙ) D' ])
AntiRedLog (Emptyᵣ [ ⊢A , ⊢Empty , D ]) [ ⊢A' , ⊢B , D' ] = Emptyᵣ ([ ⊢B , ⊢Empty , whrDet↘ (D , Emptyₙ) D' ])
AntiRedLog (Unitᵣ [ ⊢A , ⊢Unit , D ]) [ ⊢A' , ⊢B , D' ] = Unitᵣ ([ ⊢B , ⊢Unit , whrDet↘ (D , Unitₙ) D' ])
AntiRedLog (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) [ ⊢A' , ⊢B , D' ] = ne (ne K ([ ⊢B , ⊢K , whrDet↘ (D , ne neK) D' ]) neK K≡K)
AntiRedLog (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) ([ ⊢A' , ⊢B , D' ]) =
  Bᵣ W (Bᵣ F G ([ ⊢B , ⊢Π , whrDet↘ (D , ⟦ W ⟧ₙ) D' ]) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
AntiRedLog (emb {l} {lε} {A}  0<1 [A]) D = emb 0<1 (AntiRedLog [A] D)  
AntiRedLog (ϝᵣ mε [ ⊢A , ⊢B , D ] αB  tB fB) [ ⊢A' , ⊢B' , D' ] = ϝᵣ mε ([ ⊢B' , ⊢B , whrDet↘ (D , αₙ αB) D' ]) αB tB fB 


RedConvℕ : ∀ {A B C} k ([C] : Γ / lε ⊩ℕ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / ℕᵣ [C]) →  Γ / lε ⊢ A :⇒*: B
             →  Γ / lε ⊩⟨ k ⟩ C ≡ A / ℕᵣ [C]
RedConvℕ k [C] (⊩ℕ≡ _ B B⇒ℕ) [ ⊢A' , ⊢B , D' ] = ⊩ℕ≡ _ _ (⇒*-comp D' B⇒ℕ)
RedConvℕ k [C] (ϝ⊩ℕ≡ mε B⇒B' αB' tC≡B fC≡B) A⇒B =
 ϝ⊩ℕ≡ mε [ ⊢A-red A⇒B , ⊢B-red B⇒B' , ⇒*-comp (red A⇒B) (red B⇒B') ] αB' tC≡B fC≡B 

RedConvW : ∀ {A B C} k W ([C] : Γ / lε ⊩′⟨ k ⟩B⟨ W ⟩ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / Bᵣ W [C]) →  Γ / lε ⊢ A :⇒*: B
             →  Γ / lε ⊩⟨ k ⟩ C ≡ A / Bᵣ W [C]
RedConvW k W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' B≡C [F≡F'] [G≡G']) A⇒B =
  B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (⇒*-comp (red A⇒B) D') B≡C [F≡F'] [G≡G']
RedConvW k W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ [C] [C]t [C]f tB≡C fB≡C) A⇒B =
  Bϝ [C] [C]t [C]f (RedConvW k W [C]t tB≡C (τwfRed* A⇒B)) (RedConvW k W [C]f fB≡C (τwfRed* A⇒B))


RedConvLog : ∀ {k A B C} ([C] :  Γ / lε ⊩⟨ k ⟩ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / [C]) →  Γ / lε ⊢ A :⇒*: B
             →  Γ / lε ⊩⟨ k ⟩ C ≡ A / [C]
RedConvLog (Uᵣ′ k′ k< ⊢Γ) B≡U A⇒B rewrite B≡U = redU* (red A⇒B)
RedConvLog {k = k} (ℕᵣ [C]) B≡ℕ D = RedConvℕ k [C] B≡ℕ D
RedConvLog (Emptyᵣ x₁) C≡B D = ⇒*-comp (red D) C≡B
RedConvLog (Unitᵣ x₁) C≡B D = ⇒*-comp (red D) C≡B
RedConvLog (ne (ne K D neK K≡K)) (ne₌ _ D' neM M≡M) A⇒B = ne₌ _ ([ ⊢A-red A⇒B , ⊢B-red D' , ⇒*-comp (red A⇒B) (red D') ]) neM M≡M
RedConvLog {k = k} (Bᵣ W [C]) B≡C A⇒B = RedConvW k W [C] B≡C A⇒B
RedConvLog (emb 0<1 [A]) C≡B D = RedConvLog [A] C≡B D
RedConvLog (ϝᵣ { B = D } mε C⇒D αD [D]t [D]f) ( tC≡B , fC≡B ) A⇒B =
  RedConvLog [D]t tC≡B (τwfRed* A⇒B) , RedConvLog [D]f fC≡B (τwfRed* A⇒B)

TyLog≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') {k A}
           → ([A] :  Γ / lε ⊩⟨ k ⟩ A) → Γ / lε' ⊩⟨ k ⟩ A
TyLog≤ f< (Uᵣ′ k′ k< ⊢Γ) = Uᵣ′ k′ k<  (Con≤ f< ⊢Γ)
TyLog≤ f< (ℕᵣ [ ⊢A , ⊢ℕ , D ]) = ℕᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢ℕ , Red≤* f< D ])
TyLog≤ f< (Emptyᵣ [ ⊢A , ⊢Empty , D ]) = Emptyᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Empty , Red≤* f< D ])
TyLog≤ f< (Unitᵣ [ ⊢A , ⊢Unit , D ]) = Unitᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Unit , Red≤* f< D ])
TyLog≤ f< (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) = ne (ne K ([ Ty≤ f< ⊢A , Ty≤ f< ⊢K , Red≤* f< D ]) neK (~-≤ f< K≡K))
TyLog≤ {l = l} {l' = l'} f< (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) =
  Bᵣ W (Bᵣ F G ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Π , Red≤* f< D ]) (Ty≤ f< ⊢F) (Ty≤ f< ⊢G) (≅-≤ f< A≡A) [F] (λ {m} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (f< n b inl)}) G-ext)
TyLog≤ f< (emb {l} {lε} {A}  0<1 [A]) = emb 0<1 (TyLog≤ f< [A]) 
TyLog≤ {l' = l'} f< (ϝᵣ {m = m} mε [ ⊢A , ⊢B , D ] αB tB fB) with decidInLConNat l' m  
TyLog≤ f< (ϝᵣ {m = m} mε [ ⊢A , ⊢B , D ] αB tB fB)  | TS.inj₁ (TS.inj₁ inl) =
  escapeAux (TyLog≤ (≤ₗ-add _ _ _ f< inl) tB) ([ Ty≤ f< ⊢A , Ty≤ f< ⊢B , Red≤* f< D ])
TyLog≤ f< (ϝᵣ {m = m} mε [ ⊢A , ⊢B , D ] αB tB fB)  | TS.inj₁ (TS.inj₂ inl) =
  escapeAux (TyLog≤ (≤ₗ-add _ _ _ f< inl) fB) ([ Ty≤ f< ⊢A , Ty≤ f< ⊢B , Red≤* f< D ])
TyLog≤ f< (ϝᵣ {m = m} mε [ ⊢A , ⊢B , D ] αB tB fB)  | TS.inj₂ notinl'  =
  (ϝᵣ notinl' ([ Ty≤ f< ⊢A , Ty≤ f< ⊢B , Red≤* f< D ]) (αNeNotIn notinl' αB)
    (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) tB)
    (TyLog≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) fB)) 



-- Reducible types are well-formed.
escape : ∀ {k A} → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊢ A
escape (Uᵣ′ k′ k< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (ϝᵣ mε [ ⊢A , ⊢B , D ] αB  tB fB) = ⊢A -- ϝⱼ (escape (escapeAux {!!} {!!})) (escape {!!})
escape (emb 0<1 A) = escape A
      
-- Reducible type equality respect the equality relation.

reflEqAux : ∀ {k A B} ([B] :  Γ / lε ⊩⟨ k ⟩ B) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ B ≡ A / [B]
reflEqAux (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite redU* D' = PE.refl
reflEqAux (ℕᵣ [ ⊢B , ⊢ℕ , D ]) [ ⊢A , ⊢B' , D' ] = ⊩ℕ≡ _ _ (red ( [ ⊢A , ⊢ℕ , ⇒*-comp D' D ] ))
reflEqAux (Emptyᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = ⇒*-comp D' D
reflEqAux (Unitᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = ⇒*-comp D' D
reflEqAux (ne (ne K [ ⊢A' , ⊢K , D ] neK K≡K)) [ ⊢A , ⊢B , D' ] = ne₌ _ [ ⊢A , ⊢K , ⇒*-comp D' D ] neK K≡K
reflEqAux (Bᵣ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) [ ⊢A , ⊢B , D' ] =
  B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (⇒*-comp D' (red D)) A≡A
    (λ {m} {_} {_} {l'} {≤ε} {lε'} ρ Δ → reflEqAux ([F] ρ Δ) (idRed:*: (Definition.Typed.Weakening.wk ρ Δ (Ty≤ ≤ε ⊢F))))
    λ {m} {ρ} {_} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] → reflEqAux ([G] [ρ] ⊢Δ [a]) (idRed:*: (escape ([G] [ρ] ⊢Δ [a])))
--  B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (⇒*-comp D' (red D)) A≡A
--    (λ {m} {_} {_} {l'} {≤ε} {lε'} ρ Δ → reflEqAux ([F] ρ Δ) (idRed:*: (Definition.Typed.Weakening.wk ρ Δ (Ty≤ ≤ε ⊢F))))
--    λ {m} {ρ} {_} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] → reflEqAux ([G] [ρ] ⊢Δ [a]) {!!}
reflEqAux (emb 0<1 [A]) D = reflEqAux [A] D
reflEqAux (ϝᵣ {B = B} mε ([ ⊢A , ⊢B , D ]) αB [B] [B]₁) [ ⊢A' , ⊢B' , D' ] =
  reflEqAux [B] ([ τTy _ _ _ _ ⊢A' , τTy _ _ _ _ ⊢B , ⇒*-comp (τRed* D') (τRed* D) ]) ,
  reflEqAux [B]₁ ([ τTy _ _ _ _ ⊢A' , τTy _ _ _ _ ⊢B , ⇒*-comp (τRed* D') (τRed* D) ])




escapeEq : ∀ {k A B} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
            → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
            → Γ / lε ⊢ A ≅ B
escapeEq (Uᵣ′ k′ k< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
escapeEq {k = k} (ℕᵣ D) A=B  = LogRel.escapeEqℕ k (logRelRec _) D A=B
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
escapeEq (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             A=B = LogRel.escapeEqB k (logRelRec _) (Bᵣ _ _ D ⊢F ⊢G A≡A [F] [G] G-ext) A=B
  -- ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B
escapeEq (ϝᵣ mε [ ⊢A , ⊢B , D ] αB  tB fB) ( x , y ) =
  ≅-trans (≅-red D (id ⊢B) (αₙ αB) (αₙ αB) (≅-ϝ (escapeEq tB (reflEqAux tB (idRed:*: (τTy _ _ _ _ ⊢B)))) (escapeEq fB (reflEqAux fB (idRed:*: (τTy _ _ _ _ ⊢B))))))
          (≅-ϝ (escapeEq tB x) (escapeEq fB y))

-- Reducible terms are well-formed.
escapeTerm : ∀ {k A t} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
              → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
              → Γ / lε ⊢ t ∷ A
escapeTerm (Uᵣ′ k′ k< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Unitᵣ D) (Unitₜ e [ ⊢t , ⊢u , d ] prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Πₜ f [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Σₜ p [ ⊢t , ⊢u , d ] pProd p≅p [fst] [snd]) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ϝᵣ mε A⇒B αB  tB fB) ( x , y ) = conv (ϝⱼ (escapeTerm tB x) (escapeTerm fB y)) (sym (subset* (red A⇒B))) --  ϝⱼ (escapeTerm {!!} x) (escapeTerm {!!} y)
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {k A t u} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A]
                → Γ / lε ⊢ t ≅ u ∷ A
escapeTermEq (Uᵣ′ k′ k< ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
             (ne natK) (ne natK′) k≡k′
escapeTermEq {k} {Γ} {A} {t} {u} (Unitᵣ D) (Unitₜ₌ ⊢t ⊢u) =
  let t≅u = ≅ₜ-η-unit ⊢t ⊢u
      A≡Unit = subset* (red D)
  in  ≅-conv t≅u (sym A≡Unit)
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [fstp] [fstr] [fst≡] [snd≡]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Σₙ (productWhnf pProd) (productWhnf rProd) p≅r
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u 
escapeTermEq (ϝᵣ mε A⇒B αB  tB fB) ( x , y ) = ≅-conv (≅ₜ-ϝ (escapeTermEq tB x) (escapeTermEq fB y)) (sym (subset* (red A⇒B)))
