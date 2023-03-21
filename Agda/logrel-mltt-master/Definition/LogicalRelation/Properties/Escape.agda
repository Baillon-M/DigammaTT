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



-- ConvLog-ϝ : ∀ {A B k k' k'' n nε} {[A]t [A]f} [A]
--                          → Γ / ⊢ₗ• l lε n Btrue nε ⊩⟨ k ⟩ A ≡ B / [A]t
--                          → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k' ⟩ A ≡ B / [A]f
--                          →  Γ / lε ⊩⟨ k'' ⟩ A ≡ B / [A]
-- ConvLog-ϝ (ℕᵣ D) tAB fAB = ϝ⊩ℕ≡ {!!} {!!} {!!} {!!} {!!}
-- ConvLog-ϝ (Uᵣ x₂) x x₁
-- ConvLog-ϝ (𝔹ᵣ x₂) x x₁
-- ConvLog-ϝ (ne x₂) x x₁
-- ConvLog-ϝ (Bᵣ W x₂) x x₁
-- ConvLog-ϝ (emb j< [A]) x x₁
-- ConvLog-ϝ (ϝᵣ mε x₂ x₃ [A] [A]₁) x x₁

TyLog≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') {k A}
           → ([A] :  Γ / lε ⊩⟨ k ⟩ A) → Γ / lε' ⊩⟨ k ⟩ A
TyLog≤ f< (Uᵣ′ k′ k< ⊢Γ) = Uᵣ′ k′ k<  (Con≤ f< ⊢Γ)
TyLog≤ f< (ℕᵣ [ ⊢A , ⊢ℕ , D ]) = ℕᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢ℕ , Red≤* f< D ])
TyLog≤ f< (𝔹ᵣ [ ⊢A , ⊢𝔹 , D ]) = 𝔹ᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢𝔹 , Red≤* f< D ])
-- TyLog≤ f< (Emptyᵣ [ ⊢A , ⊢Empty , D ]) = Emptyᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Empty , Red≤* f< D ])
-- TyLog≤ f< (Unitᵣ [ ⊢A , ⊢Unit , D ]) = Unitᵣ ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Unit , Red≤* f< D ])
TyLog≤ f< (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) = ne (ne K ([ Ty≤ f< ⊢A , Ty≤ f< ⊢K , Red≤* f< D ]) neK (~-≤ f< K≡K))
TyLog≤ {l = l} {l' = l'} f< (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) =
  Bᵣ W (Bᵣ F G ([ Ty≤ f< ⊢A , Ty≤ f< ⊢Π , Red≤* f< D ]) (Ty≤ f< ⊢F) (Ty≤ f< ⊢G) (≅-≤ f< A≡A)
    (λ {m} {ρ} {Δ} [ρ] → let N , [F]' = [F] [ρ] in N , λ ≤ε lε'' N<s ⊢Δ → [F]' (≤ₗ-• f< ≤ε) lε'' N<s ⊢Δ)
    (λ [ρ] ≤ε lε'' N<s ⊢Δ [a] → [G] [ρ] (≤ₗ-• f< ≤ε) lε'' N<s ⊢Δ [a])
    λ [ρ] ≤ε lε'' N<s ⊢Δ [a] [b] a≡b ≤ε' lε''' M<s → G-ext [ρ] (≤ₗ-• f< ≤ε) lε'' N<s ⊢Δ [a] [b] a≡b ≤ε' lε''' M<s) --[F]
    -- (λ {m} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (f< n b inl)}) G-ext)
TyLog≤ f< (emb {l} {lε} {A}  0<1 [A]) = emb 0<1 (TyLog≤ f< [A])

τTyLog : ∀ {l : LCon} {lε : ⊢ₗ l} {n b nε k A}
           → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
           → Γ / ⊢ₗ• l lε n b nε ⊩⟨ k ⟩ A
τTyLog [A] = TyLog≤ (λ m b' mε → InThereNat _ mε _ _) [A]



AntiRedLog : ∀ {k A B} ([B] :  Γ / lε ⊩⟨ k ⟩ B) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ A
AntiRedLog (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite redU* D' = Uᵣ′ k′ k< ⊢Γ
AntiRedLog (ℕᵣ [ ⊢B , ⊢ℕ , D ]) [ ⊢A , ⊢B' , D' ] = ℕᵣ ([ ⊢A , ⊢ℕ , ⇒*-comp D' D ])
AntiRedLog (𝔹ᵣ [ ⊢B , ⊢𝔹 , D ]) [ ⊢A , ⊢B' , D' ] = 𝔹ᵣ ([ ⊢A , ⊢𝔹 , ⇒*-comp D' D ])
-- AntiRedLog (Emptyᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = Emptyᵣ ([ ⊢A , ⊢Empty , ⇒*-comp D' D ])
-- AntiRedLog (Unitᵣ [ ⊢B , ⊢Unit , D ]) [ ⊢A , ⊢B' , D' ] = Unitᵣ ([ ⊢A , ⊢Unit , ⇒*-comp D' D ])
AntiRedLog (ne (ne K [ ⊢B , ⊢K , D ] neK K≡K)) [ ⊢A , ⊢B' , D' ] = ne (ne K ([ ⊢A , ⊢K , ⇒*-comp D' D ]) neK K≡K)
AntiRedLog (Bᵣ W (Bᵣ F G [ ⊢B , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) ([ ⊢A , ⊢B' , D' ]) =
  Bᵣ W (Bᵣ F G ([ ⊢A , ⊢Π , ⇒*-comp D' D ]) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
AntiRedLog (emb {l} {lε} {A}  0<1 [A]) D = emb 0<1 (AntiRedLog [A] D)  


RedLog : ∀ {k A B} ([A] :  Γ / lε ⊩⟨ k ⟩ A) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ B
RedLog (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite PE.sym (whnfRed* D' Uₙ) = Uᵣ′ _ k< ⊢Γ -- Uᵣ′ k′ k< ⊢Γ
RedLog (ℕᵣ [ ⊢A , ⊢ℕ , D ]) [ ⊢A' , ⊢B , D' ] = ℕᵣ ([ ⊢B , ⊢ℕ , whrDet↘ (D , ℕₙ) D' ])
RedLog (𝔹ᵣ [ ⊢A , ⊢𝔹 , D ]) [ ⊢A' , ⊢B , D' ] = 𝔹ᵣ ([ ⊢B , ⊢𝔹 , whrDet↘ (D , 𝔹ₙ) D' ])
-- RedLog (Emptyᵣ [ ⊢A , ⊢Empty , D ]) [ ⊢A' , ⊢B , D' ] = Emptyᵣ ([ ⊢B , ⊢Empty , whrDet↘ (D , Emptyₙ) D' ])
-- RedLog (Unitᵣ [ ⊢A , ⊢Unit , D ]) [ ⊢A' , ⊢B , D' ] = Unitᵣ ([ ⊢B , ⊢Unit , whrDet↘ (D , Unitₙ) D' ])
RedLog (ne (ne K [ ⊢A , ⊢K , D ] neK K≡K)) [ ⊢A' , ⊢B , D' ] = ne (ne K ([ ⊢B , ⊢K , whrDet↘ (D , ne neK) D' ]) neK K≡K)
RedLog (Bᵣ W (Bᵣ F G [ ⊢A , ⊢Π , D ] ⊢F ⊢G A≡A [F] [G] G-ext)) ([ ⊢A' , ⊢B , D' ]) =
  Bᵣ W (Bᵣ F G ([ ⊢B , ⊢Π , whrDet↘ (D , ⟦ W ⟧ₙ) D' ]) ⊢F ⊢G A≡A (λ {m} {l'} {≤ε} → [F] {m} {l'} {≤ε}) [G] G-ext)
RedLog (emb {l} {lε} {A}  0<1 [A]) D = emb 0<1 (RedLog [A] D)  

-- AntiRedConvℕ : ∀ {A B C} k ([C] : Γ / lε ⊩ℕ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / ℕᵣ [C]) →  Γ / lε ⊢ A :⇒*: B
--              →  Γ / lε ⊩⟨ k ⟩ C ≡ A / ℕᵣ [C]
-- AntiRedConvℕ k [C] (⊩ℕ≡ _ B B⇒ℕ) [ ⊢A' , ⊢B , D' ] = ⊩ℕ≡ _ _ (⇒*-comp D' B⇒ℕ)
-- AntiRedConvℕ k [C] (ϝ⊩ℕ≡ mε B⇒B' αB' tC≡B fC≡B) A⇒B =
--  ϝ⊩ℕ≡ mε (:⇒:*-comp A⇒B B⇒B') αB'
--    (AntiRedConvℕ k (τwfRed* [C]) tC≡B (τwfRed* A⇒B))
--    (AntiRedConvℕ k (τwfRed* [C]) fC≡B (τwfRed* A⇒B))
   
-- AntiRedConv𝔹 : ∀ {A B C} k ([C] : Γ / lε ⊩𝔹 C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / 𝔹ᵣ [C]) →  Γ / lε ⊢ A :⇒*: B
--              →  Γ / lε ⊩⟨ k ⟩ C ≡ A / 𝔹ᵣ [C]
-- AntiRedConv𝔹 k [C] (⊩𝔹≡ _ B B⇒𝔹) [ ⊢A' , ⊢B , D' ] = ⊩𝔹≡ _ _ (⇒*-comp D' B⇒𝔹)
-- AntiRedConv𝔹 k [C] (ϝ⊩𝔹≡ mε B⇒B' αB' tC≡B fC≡B) A⇒B =
--  ϝ⊩𝔹≡ mε (:⇒:*-comp A⇒B B⇒B') αB'
--   (AntiRedConv𝔹 k (τwfRed* [C]) tC≡B (τwfRed* A⇒B))
--   (AntiRedConv𝔹 k (τwfRed* [C]) fC≡B (τwfRed* A⇒B))

-- AntiRedConvNe : ∀ {A B C} k ([C] : Γ / lε ⊩ne C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / ne [C]) →  Γ / lε ⊢ A :⇒*: B
--              →  Γ / lε ⊩⟨ k ⟩ C ≡ A / ne [C]
-- AntiRedConvNe k (ne K D neK K≡K) (ne₌ [A] _ D' neM M≡M) A⇒B = ne₌ _ _ ([ ⊢A-red A⇒B , ⊢B-red D' , ⇒*-comp (red A⇒B) (red D') ]) neM M≡M
-- AntiRedConvNe k (ne K D neK K≡K) (ϝ⊩ne≡ mε {[A]t = [C]t} {[A]f = [C]f} B⇒B' αB tC≡B fC≡B) A⇒B =
--   ϝ⊩ne≡ mε (:⇒:*-comp A⇒B B⇒B') αB
--     (AntiRedConvNe k [C]t tC≡B (τwfRed* A⇒B))
--     (AntiRedConvNe k [C]f fC≡B (τwfRed* A⇒B))

-- AntiRedConvW : ∀ {A B C} k W ([C] : Γ / lε ⊩′⟨ k ⟩B⟨ W ⟩ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / Bᵣ W [C]) →  Γ / lε ⊢ A :⇒*: B
--              →  Γ / lε ⊩⟨ k ⟩ C ≡ A / Bᵣ W [C]
-- AntiRedConvW k W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (B₌ _ _ _ _ _ _ _ _ _ F' G' D' B≡C [F≡F'] [G≡G']) A⇒B =
--   B₌ F G D ⊢F ⊢G A≡A [F] [G] G-ext _ _ (⇒*-comp (red A⇒B) D') B≡C [F≡F'] [G≡G']
-- AntiRedConvW k W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bϝ [C] B⇒B' αB' [C]t [C]f tB≡C fB≡C) A⇒B =
--   Bϝ [C] (:⇒:*-comp A⇒B B⇒B') αB' [C]t [C]f
--     (AntiRedConvW k W [C]t tB≡C (τwfRed* A⇒B))
--     (AntiRedConvW k W [C]f fB≡C (τwfRed* A⇒B)) -- ([ ⊢A-red A⇒B , ⊢B-red B⇒B' , ⇒*-comp (red A⇒B) (red B⇒B') ]) αB' [C]t [C]f (AntiRedConvW k W [C]t tB≡C (τwfRed* (idRed:*: (⊢B-red B⇒B')))) (AntiRedConvW k W [C]f fB≡C (τwfRed* (idRed:*: (⊢B-red B⇒B'))))


AntiRedConvLog : ∀ {k A B C} ([C] :  Γ / lε ⊩⟨ k ⟩ C) (C≡B :  Γ / lε ⊩⟨ k ⟩ C ≡ B / [C]) →  Γ / lε ⊢ A :⇒*: B
             →  Γ / lε ⊩⟨ k ⟩ C ≡ A / [C]
AntiRedConvLog (Uᵣ′ k′ k< ⊢Γ) (⊩¹≡U B B≡U) A⇒B rewrite B≡U = ⊩¹≡U B (redU* (red A⇒B)) --redU* (red A⇒B)
AntiRedConvLog {k = k} (ℕᵣ [C]) (⊩¹≡ℕ _ B≡ℕ) D = ⊩¹≡ℕ [C] (⇒*-comp (red D) B≡ℕ) -- AntiRedConvℕ k [C] B≡ℕ D
AntiRedConvLog {k = k} (𝔹ᵣ [C]) (⊩¹≡𝔹 _ B≡𝔹) D = ⊩¹≡𝔹 [C] (⇒*-comp (red D) B≡𝔹) -- AntiRedConv𝔹 k [C] B≡𝔹 D
-- AntiRedConvLog (Emptyᵣ x₁) C≡B D = ⇒*-comp (red D) C≡B
-- AntiRedConvLog (Unitᵣ x₁) C≡B D = ⇒*-comp (red D) C≡B
AntiRedConvLog {k = k} (ne neC) (⊩¹≡ne _ (ne₌ M D' neM K≡M)) A⇒B = ⊩¹≡ne neC (ne₌ M (:⇒:*-comp A⇒B D') neM K≡M) -- AntiRedConvNe k neC B≡C A⇒B
AntiRedConvLog {k = k} (Bᵣ W [C]) (⊩¹≡B W _ (B₌ F' G' D' A≡B [F≡F'] [G≡G'])) A⇒B = ⊩¹≡B W [C] (B₌ F' G' (⇒*-comp (red A⇒B) D') A≡B [F≡F'] [G≡G']) 
AntiRedConvLog (emb 0<1 [A]) (⊩¹≡emb j< [A] C≡B) D = ⊩¹≡emb 0<1 [A] (AntiRedConvLog [A] C≡B D)


-- TyLogU : ∀ {l : LCon} {lε : ⊢ₗ l} {k}
--            → ([A] :  Γ / lε ⊩⟨ k ⟩ U)
--            → ∃ (λ K → [A] PE.≡ Uᵣ K)
-- TyLogU (Uᵣ K) = K , PE.refl
-- TyLogU (ℕᵣ D) with whnfRed* (red D) Uₙ
-- ... | ()
-- TyLogU (𝔹ᵣ D) with whnfRed* (red D) Uₙ
-- ... | ()
-- -- TyLogU (Emptyᵣ D) with whnfRed* (red D) Uₙ
-- -- ... | ()
-- -- TyLogU (Unitᵣ D) with whnfRed* (red D) Uₙ
-- -- ... | ()
-- TyLogU (ne′ K D neK K≡K) =
--   PE.⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- TyLogU (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
--   PE.⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- TyLogU (emb 0<1 x) with TyLogU x
-- TyLogU (emb 0<1 x) | (Uᵣ _ () _) , e
-- TyLogU (ϝᵣ mε tA fA) = {!!} -- PE.⊥-elim (U≢αne αB (whnfRed* (red A⇒B) Uₙ))
 

-- Reducible types are well-formed.
escape : ∀ {k A} → Γ / lε ⊩⟨ k ⟩ A → Γ / lε ⊢ A
escape (Uᵣ′ k′ k< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (𝔹ᵣ [ ⊢A , ⊢B , D ]) = ⊢A
-- escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
-- escape (Unitᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ W F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (emb 0<1 A) = escape A
      
-- Reducible type equality respect the equality relation.

reflEqAux : ∀ {k A B} ([B] :  Γ / lε ⊩⟨ k ⟩ B) →  Γ / lε ⊢ A :⇒*: B →  Γ / lε ⊩⟨ k ⟩ B ≡ A / [B]
reflEqAux (Uᵣ′ k′ k< ⊢Γ) [ ⊢A , ⊢B' , D' ] rewrite redU* D' = ⊩¹≡U (Uᵣ k′ k< ⊢Γ) PE.refl -- PE.refl
reflEqAux (ℕᵣ D) D' = ⊩¹≡ℕ D (⇒*-comp (red D') (red D)) -- ⊩ℕ≡ _ _ (red ( [ ⊢A , ⊢ℕ , ⇒*-comp D' D ] ))
reflEqAux (𝔹ᵣ D) D' = ⊩¹≡𝔹 D (⇒*-comp (red D') (red D)) -- ⊩𝔹≡ _ _ (red ( [ ⊢A , ⊢𝔹 , ⇒*-comp D' D ] ))
-- reflEqAux (Emptyᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = ⇒*-comp D' D
-- reflEqAux (Unitᵣ [ ⊢B , ⊢Empty , D ]) [ ⊢A , ⊢B' , D' ] = ⇒*-comp D' D
reflEqAux (ne (ne K D neK K≡K)) D' = ⊩¹≡ne (ne K D neK K≡K) (ne₌ K (:⇒:*-comp D' D) neK K≡K) --  ne₌ _ _ [ ⊢A , ⊢K , ⇒*-comp D' D ] neK K≡K
reflEqAux (Bᵣ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) D' =
  ⊩¹≡B W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
    (B₌ F G (⇒*-comp (red D') (red D)) A≡A
      (λ [ρ] ≤ε lε' N<s → let N , [F]₂ = [F] [ρ] in N , λ ≤ε' lε'' M<s ⊢Δ →
         let [[F]] = [F]₂ (≤ₗ-• ≤ε ≤ε') lε'' (≤-trans N<s (≤ₗ-size lε' ≤ε')) ⊢Δ
         in reflEqAux [[F]] (idRed:*: (escape [[F]])))
      (λ [ρ] ≤ε lε' N<s ⊢Δ [a] ≤ε' lε'' M<s → let M , [G]₂ = [G] [ρ] ≤ε lε' N<s ⊢Δ [a] in M , λ ≤ε'' lε'' M<s →
         let [[G]] = [G]₂ (≤ₗ-• ≤ε' ≤ε'') lε'' _ in reflEqAux [[G]] (idRed:*: (escape [[G]]))))
      -- (λ {m} {_} {_} {l'} {≤ε} {lε'} ρ Δ → reflEqAux ([F] ρ Δ) (idRed:*: (escape ([F] {≤ε = ≤ε} ρ Δ))))
      -- λ {m} {ρ} {_} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] → reflEqAux ([G] [ρ] ⊢Δ [a]) (idRed:*: (escape ([G] [ρ] ⊢Δ [a])))) 
reflEqAux (emb 0<1 [A]) D = ⊩¹≡emb 0<1 [A] (reflEqAux [A] D) -- reflEqAux [A] D




escapeEq : ∀ {k A B} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
            → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
            → Γ / lε ⊢ A ≅ B
escapeEq (Uᵣ′ k′ k< ⊢Γ) (⊩¹≡U _ A=B) rewrite A=B = ≅-Urefl ⊢Γ
escapeEq {k = k} (ℕᵣ D) (⊩¹≡ℕ _ A=B)  = LogRel.escapeEqℕ k (logRelRec _) D A=B
escapeEq {k = k} (𝔹ᵣ D) (⊩¹≡𝔹 _ A=B)  = LogRel.escapeEq𝔹 k (logRelRec _) D A=B
-- escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
-- escapeEq (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
escapeEq {k = k} (ne neA) (⊩¹≡ne _ A=B) = LogRel.escapeEqNe k (logRelRec _) neA A=B
escapeEq {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (⊩¹≡B W _ A=B) = LogRel.escapeEqB k (logRelRec _) (Bᵣ _ _ D ⊢F ⊢G A≡A [F] [G] G-ext) A=B
  -- ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
escapeEq (emb 0<1 A) (⊩¹≡emb 0<1 _ A≡B) = escapeEq A A≡B


-- Reducible terms are well-formed.
escapeTerm : ∀ {k A t} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
              → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
              → Γ / lε ⊢ t ∷ A
escapeTerm (Uᵣ′ k′ k< ⊢Γ) (Uₜ ⊢t t≡t [A]) = ⊢t
escapeTerm {k = k} (ℕᵣ D) ⊢t = conv (LogRel.escapeTermℕ k (logRelRec _) ⊢t) (sym (subset* (red D)))
escapeTerm {k = k} (𝔹ᵣ D) ⊢t = conv (LogRel.escapeTerm𝔹 k (logRelRec _) ⊢t) (sym (subset* (red D)))
-- escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
--   conv ⊢t (sym (subset* (red D)))
-- escapeTerm (Unitᵣ D) (Unitₜ e [ ⊢t , ⊢u , d ] prop) =
--   conv ⊢t (sym (subset* (red D)))
escapeTerm {k = k} (ne neA) net = LogRel.escapeTermNe k (logRelRec _) neA net
escapeTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Πₜ ⊢f f≡f [f] [f]₁) =
  conv ⊢f (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Σₜ p [ ⊢t , ⊢u , d ] pProd p≅p [prop]) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t


-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {k A t u} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
                → Γ / lε ⊩⟨ k ⟩ t ≡ u ∷ A / [A]
                → Γ / lε ⊢ t ≅ u ∷ A
escapeTermEq (Uᵣ′ k′ k< ⊢Γ) (Uₜ₌ ⊢t ⊢u A≡B [A] [B] [A≡B]) =
 A≡B --  ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq {k = k} (ℕᵣ D) t≡u =
  ≅-conv (LogRel.escapeTermEqℕ k (logRelRec _) t≡u) (sym (subset* (red D)))
escapeTermEq {k = k} (𝔹ᵣ D) t≡u =
  ≅-conv (LogRel.escapeTermEq𝔹 k (logRelRec _) t≡u) (sym (subset* (red D)))
-- escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
--   let natK , natK′ = esplit prop
--   in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
--              (ne natK) (ne natK′) k≡k′
-- escapeTermEq {k} {Γ} {A} {t} {u} (Unitᵣ D) (Unitₜ₌ ⊢t ⊢u) =
--   let t≅u = ≅ₜ-η-unit ⊢t ⊢u
--       A≡Unit = subset* (red D)
--   in  ≅-conv t≅u (sym A≡Unit)
escapeTermEq {k = k} (ne neA) t=u = LogRel.escapeTermEqNe k (logRelRec _) neA t=u
escapeTermEq (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f≡g [f] [g] [f≡g]) =
  ≅-conv f≡g (sym (subset* (red D))) -- ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] [prop≡]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Σₙ (productWhnf pProd) (productWhnf rProd) p≅r
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u 


-- escapeEqLog : ∀ {k A B} → ([A] : Γ / lε ⊩⟨ k ⟩ A)
--             → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
--             → Γ / lε ⊩⟨ k ⟩ B
-- escapeEqLog (Uᵣ′ k′ k< ⊢Γ) PE.refl = {!!}
-- escapeEqLog {k = k} (ℕᵣ D) A=B  = {!!}
-- escapeEqLog {k = k} (𝔹ᵣ D) A=B  = {!!}
-- -- escapeEqLog (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
-- -- escapeEqLog (Unitᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A))
-- escapeEqLog {k = k} (ne neA) A=B = {!!}
-- escapeEqLog {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--                  Bᵣ W (Bᵣ F′ G′ [ {!!} , {!!} , D′ ] {!!} {!!} {!!}
--                      (λ {m} {l'} {f<} {lε'} {ρ} {Δ} [ρ] ⊢Δ → escapeEqLog ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
--                      (λ {m} {ρ} {Δ} {a} {l'} {f<} {lε'} [ρ] ⊢Δ [a] → escapeEqLog ([G] [ρ] ⊢Δ {!!}) {!!}) {!!})
-- escapeEqLog {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--                  (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) = ϝᵣ {!!} B⇒B' αB {!!} {!!}
-- escapeEqLog (emb 0<1 A) A≡B = emb 0<1 (escapeEqLog A A≡B)
-- escapeEqLog (ϝᵣ mε A⇒B αB tB fB) ( x , y ) = {!!}


--   -- escapeEqLogW : ∀ W {k A B} → ([A] : Γ / lε  ⊩¹B⟨ W ⟩ A)
--   --             → Γ / lε ⊩¹B⟨ W ⟩ A ≡ B / [A]
--   --             → Γ / lε ⊩¹ B
--   -- escapeEqLogW W {k = k} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   --                  (B₌ _ _ _ _ _ _ _ _ _ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
--   --                  Bᵣ W (Bᵣ F′ G′ [ {!!} , {!!} , D′ ] {!!} {!!} {!!}
--   --                    (λ {m} {l'} {f<} {lε'} {ρ} {Δ} [ρ] ⊢Δ → {!!}) {!!} {!!})
--   -- escapeEqLogW W {k = k} (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   --                  (Bϝ [C] B⇒B' αB [A]t [A]f tA≡B fA≡B) = ϝᵣ {!!} B⇒B' αB (escapeEqLogW W [A]t tA≡B) (escapeEqLogW W [A]f fA≡B)
