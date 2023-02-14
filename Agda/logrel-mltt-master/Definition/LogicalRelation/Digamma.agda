{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Digamma {{eqrel : EqRelSet}} where
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

ϝℕ : ∀ {A t k k′ k″ n nε} ℕA
     (p : Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ A) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ A)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ A / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ A / q
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / ℕᵣ ℕA
ϝℕ {k = k} ℕA p q tt ft with goodCasesRefl {k = k} (ℕᵣ (τwfRed* ℕA)) p with goodCasesRefl {k = k} (ℕᵣ (τwfRed* ℕA)) q
ϝℕ {k = k} ℕA p q tt ft
  | ℕᵥ tℕA tℕA′ tℕA≡B | ℕᵥ fℕB fℕB′ fℕA≡B = ℕϝ tt ft
ϝℕ {k = k} ℕA p (emb 0<1 q) tt ft
  | ℕᵥ tℕA tℕA′ tℕA≡B | emb¹⁰ fA = ϝℕ {k = k} ℕA p q tt ft
ϝℕ {k = k} ℕA p q tt ( tft , fft)
  | ℕᵥ tℕA tℕA′ tℕA≡B | ϝᵣ-r (ℕᵣ ℕA′) ℕAt ℕAf tp fp A≡B tA≡B fA≡B tAB fAB = ℕϝ tt (ϝℕ {k = k} ℕA′ tp fp tft fft)
ϝℕ {k = k} ℕA (emb 0<1 p) q tt ft
  | emb¹⁰ [A] | _ = ϝℕ {k = k} ℕA p q tt ft
ϝℕ {k = k} ℕA (ϝᵣ mε tp fp) q ( ttt , ftt) ft
  | ϝᵣ-r (ℕᵣ ℕA′) ℕAt ℕAf tp fp A≡B tA≡B fA≡B tAB fAB
  | ℕᵥ fℕB fℕB′ fℕA≡B = ℕϝ (ϝℕ {k = k} ℕA′ tp fp ttt ftt) ft
ϝℕ {k = k} ℕA (ϝᵣ mε tp fp) (emb 0<1 q) tt ft
  | ϝᵣ-r (ℕᵣ ℕA′) ℕAt ℕAf tp fp A≡B tA≡B fA≡B tAB fAB
  | emb¹⁰ fA  = ϝℕ {k = k} ℕA (ϝᵣ mε tp fp) q tt ft
ϝℕ {k = k} ℕA (ϝᵣ mε tp fp) q ( ttt , ftt ) ( tft , fft )
  | ϝᵣ-r (ℕᵣ ℕA′) tℕAt tℕAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
  | ϝᵣ-r (ℕᵣ ℕA″) fℕAt fℕAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = ℕϝ (ϝℕ {k = k} ℕA′ ttp tfp ttt ftt) (ϝℕ {k = k} ℕA″ ftp ffp tft fft)


ϝ𝔹 : ∀ {A t k k′ k″ n nε} 𝔹A
     (p : Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ A) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ A)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ A / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ A / q
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / 𝔹ᵣ 𝔹A
ϝ𝔹 {k = k} 𝔹A p q tt ft with goodCasesRefl {k = k} (𝔹ᵣ (τwfRed* 𝔹A)) p with goodCasesRefl {k = k} (𝔹ᵣ (τwfRed* 𝔹A)) q
ϝ𝔹 {k = k} 𝔹A p q tt ft
  | 𝔹ᵥ t𝔹A t𝔹A′ t𝔹A≡B | 𝔹ᵥ f𝔹B f𝔹B′ f𝔹A≡B = 𝔹ϝ tt ft
ϝ𝔹 {k = k} 𝔹A p (emb 0<1 q) tt ft
  | 𝔹ᵥ t𝔹A t𝔹A′ t𝔹A≡B | emb¹⁰ fA = ϝ𝔹 {k = k} 𝔹A p q tt ft
ϝ𝔹 {k = k} 𝔹A p q tt ( tft , fft)
  | 𝔹ᵥ t𝔹A t𝔹A′ t𝔹A≡B | ϝᵣ-r (𝔹ᵣ 𝔹A′) 𝔹At 𝔹Af tp fp A≡B tA≡B fA≡B tAB fAB = 𝔹ϝ tt (ϝ𝔹 {k = k} 𝔹A′ tp fp tft fft)
ϝ𝔹 {k = k} 𝔹A (emb 0<1 p) q tt ft
  | emb¹⁰ [A] | _ = ϝ𝔹 {k = k} 𝔹A p q tt ft
ϝ𝔹 {k = k} 𝔹A (ϝᵣ mε tp fp) q ( ttt , ftt) ft
  | ϝᵣ-r (𝔹ᵣ 𝔹A′) 𝔹At 𝔹Af tp fp A≡B tA≡B fA≡B tAB fAB
  | 𝔹ᵥ f𝔹B f𝔹B′ f𝔹A≡B = 𝔹ϝ (ϝ𝔹 {k = k} 𝔹A′ tp fp ttt ftt) ft
ϝ𝔹 {k = k} 𝔹A (ϝᵣ mε tp fp) (emb 0<1 q) tt ft
  | ϝᵣ-r (𝔹ᵣ 𝔹A′) 𝔹At 𝔹Af tp fp A≡B tA≡B fA≡B tAB fAB
  | emb¹⁰ fA  = ϝ𝔹 {k = k} 𝔹A (ϝᵣ mε tp fp) q tt ft
ϝ𝔹 {k = k} 𝔹A (ϝᵣ mε tp fp) q ( ttt , ftt ) ( tft , fft )
  | ϝᵣ-r (𝔹ᵣ 𝔹A′) t𝔹At t𝔹Af ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
  | ϝᵣ-r (𝔹ᵣ 𝔹A″) f𝔹At f𝔹Af ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = 𝔹ϝ (ϝ𝔹 {k = k} 𝔹A′ ttp tfp ttt ftt) (ϝ𝔹 {k = k} 𝔹A″ ftp ffp tft fft)

ϝU : ∀ {t k k′ k″ n nε} (N : Nat) UA
     (p : Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ U) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ U)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ U / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ U / q
     → (((μTy p) + (μTy q)) ≤ N) 
     → Γ / lε ⊩⟨ k ⟩ t ∷ U / Uᵣ UA
ϝU {k = k} N (Uᵣ j' j< ⊢Γ) p q tt ft N<
  with goodCasesRefl {k = k} (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) p
  with goodCasesRefl {k = k} (Uᵣ (Uᵣ j' j< (τCon _ _ _ _ ⊢Γ))) q
ϝU {t = t} {nε = nε} N (Uᵣ ⁰ 0<1 ⊢Γ) (Uᵣ′ _ 0<1 ⊢Γ') (Uᵣ′ _ 0<1 ⊢Γ'') (Uₜ tt tt≡t [tt]) (Uₜ ft ft≡t [ft]) N<
  | Uᵥ tUA tUA′ tUA≡B | Uᵥ fUB fUB′ fUA≡B = Uₜ (ϝⱼ tt ft) (≅ₜ-ϝ tt≡t ft≡t) (ϝᵣ nε [tt] [ft])
ϝU {k = k} (1+ N) UA p (emb 0<1 q) tt ft (≤-s N<)
  | Uᵥ tUA tUA′ tUA≡B | emb¹⁰ fA = ϝU {k = k} N UA p q tt ft N<
ϝU (1+ N) (Uᵣ ⁰ 0<1 ⊢Γ) (Uᵣ′ ⁰ 0<1 ⊢Γ') (ϝᵣ mε tp fp) (Uₜ tt tt≡t [tt]) ( tft , fft ) (≤-s N<)
  | Uᵥ tUA tUA′ tUA≡B | ϝᵣ-r (Uᵣ UA′) UAt UAf tp fp A≡B tA≡B fA≡B tAB fAB =
    let [fff]@(Uₜ f⊢t ft≡t [ft]) = ϝU N UA′ tp fp tft fft N<
    in Uₜ (ϝⱼ tt f⊢t) (≅ₜ-ϝ tt≡t ft≡t) (ϝᵣ _ [tt] [ft]) -- (ϝᵣ _ [tt] [ft])
ϝU {k = k} (1+ N) UA (emb 0<1 p) q tt ft (≤-s N<)
  | emb¹⁰ [A] | _ = ϝU {k = k} N UA p q tt ft N<
ϝU (1+ N) (Uᵣ ⁰ 0<1 ⊢Γ) (ϝᵣ mε tp fp) (Uᵣ′ ⁰ 0<1 ⊢Γ') ( ttt , ftt) (Uₜ f⊢t ft≡t [ft]) (≤-s N<)
  | ϝᵣ-r (Uᵣ UA′) UAt UAf tp fp A≡B tA≡B fA≡B tAB fAB
  | Uᵥ fUB fUB′ fUA≡B =
    let [ttt]@(Uₜ t⊢t tt≡t [tt]) = ϝU N UA′ tp fp ttt ftt (≤-trans (≤₊-l (μTy tp + μTy fp) 0) N<)
    in Uₜ (ϝⱼ t⊢t f⊢t) (≅ₜ-ϝ tt≡t ft≡t) (ϝᵣ _ [tt] [ft]) 
ϝU {k = k} (1+ N) UA (ϝᵣ mε tp fp) (emb 0<1 q) tt ft (≤-s N<)
  | ϝᵣ-r (Uᵣ UA′) UAt UAf tp fp A≡B tA≡B fA≡B tAB fAB
  | emb¹⁰ fA  = ϝU {k = k} N UA (ϝᵣ mε tp fp) q tt ft (≤-trans (≤₊-s-swap (μTy tp + μTy fp) _) N<)
ϝU (1+ N) (Uᵣ ⁰ 0<1 ⊢Γ) (ϝᵣ mε ttp tfp) (ϝᵣ mε' ftp ffp) ( ttt , ftt ) ( tft , fft ) (≤-s N<)
  | ϝᵣ-r (Uᵣ UA′) tUAt tUAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
  | ϝᵣ-r (Uᵣ UA″) fUAt fUAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB =
    let [ttt]@(Uₜ t⊢t tt≡t [tt]) = ϝU N UA′ ttp tfp ttt ftt (≤-trans (≤₊-l _ _) N<)
        [fff]@(Uₜ f⊢t ft≡t [ft]) = ϝU N UA″ ftp ffp tft fft (≤-trans (≤-suc _) (≤-trans (≤₊-r (μTy ttp + μTy tfp) _) N<))
    in Uₜ (ϝⱼ t⊢t f⊢t) (≅ₜ-ϝ tt≡t ft≡t) (ϝᵣ _ [tt] [ft])


ϝNe : ∀ {A t k k′ k″ n nε} (NeA : Γ / lε ⊩ne A)
     (p : Γ / ⊢ₗ• l lε n Btrue nε   ⊩⟨ k′ ⟩ A) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ A)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ A / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ A / q
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / ne NeA
ϝNe {k = k} (ne K D neK K≡K) p q tt ft
  with goodCasesRefl {k = k} (ne′ K (τwfRed* D) neK (~-τ K≡K)) p
  with goodCasesRefl {k = k} (ne′ K (τwfRed* D) neK (~-τ K≡K)) q
ϝNe {k = k} NeA p q tt ft
  | ne tNeA tNeA′ tNeA≡B | ne fNeB fNeB′ fNeA≡B = neϝ tt ft -- Neϝ tt ft
ϝNe {k = k} NeA p (emb 0<1 q) tt ft
  | ne tNeA tNeA′ tNeA≡B | emb¹⁰ fA = ϝNe {k = k} NeA p q tt ft
ϝNe {k = k} NeA p q tt ( tft , fft)
  | ne tNeA tNeA′ tNeA≡B | ϝᵣ-r (ne NeA′) NeAt NeAf tp fp A≡B tA≡B fA≡B tAB fAB =
  neϝ tt (ϝNe {k = k} NeA′ tp fp tft fft)
ϝNe {k = k} NeA (emb 0<1 p) q tt ft
  | emb¹⁰ [A] | _ = ϝNe {k = k} NeA p q tt ft
ϝNe {k = k} NeA (ϝᵣ mε tp fp) q ( ttt , ftt) ft
  | ϝᵣ-r (ne NeA′) NeAt NeAf tp fp A≡B tA≡B fA≡B tAB fAB
  | ne fNeB fNeB′ fNeA≡B = neϝ (ϝNe {k = k} NeA′ tp fp ttt ftt) ft
ϝNe {k = k} NeA (ϝᵣ mε tp fp) (emb 0<1 q) tt ft
  | ϝᵣ-r (ne NeA′) NeAt NeAf tp fp A≡B tA≡B fA≡B tAB fAB
  | emb¹⁰ fA  = ϝNe {k = k} NeA (ϝᵣ mε tp fp) q tt ft
ϝNe {k = k} NeA (ϝᵣ mε tp fp) q ( ttt , ftt ) ( tft , fft )
  | ϝᵣ-r (ne NeA′) tNeAt tNeAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
  | ϝᵣ-r (ne NeA″) fNeAt fNeAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB =
  neϝ (ϝNe {k = k} NeA′ ttp tfp ttt ftt) (ϝNe {k = k} NeA″ ftp ffp tft fft)

mutual
  ⊩ℕ∷ℕ≤ :  ∀ {t l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
           → Γ / lε ⊩ℕ t ∷ℕ
           → Γ / lε' ⊩ℕ t ∷ℕ
  ⊩ℕ∷ℕ≤ f< (ℕₜ n  ([ ⊢t , ⊢n , d ]) n≡n prop) =
    ℕₜ n ([ Term≤ f< ⊢t , Term≤ f< ⊢n , RedTerm≤* f< d ]) (≅ₜ-≤ n≡n f<) (Natural-prop≤ f< prop)
  ⊩ℕ∷ℕ≤ {l' = l'} f< (ℕϝ {m = m} tt ft) with decidInLConNat l' m
  ⊩ℕ∷ℕ≤ {l' = l'} f< (ℕϝ {m = m} tt ft) | TS.inj₁ (TS.inj₁ inl) = ⊩ℕ∷ℕ≤ (≤ₗ-add _ _ _ f< inl) tt
  ⊩ℕ∷ℕ≤ {l' = l'} f< (ℕϝ {m = m} tt ft) | TS.inj₁ (TS.inj₂ inl) = ⊩ℕ∷ℕ≤ (≤ₗ-add _ _ _ f< inl) ft
  ⊩ℕ∷ℕ≤ {l' = l'} f< (ℕϝ {m = m} tt ft) | TS.inj₂ notinl =
    ℕϝ {mε = notinl} (⊩ℕ∷ℕ≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) tt)
       (⊩ℕ∷ℕ≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) ft)

  Natural-prop≤ : ∀ {t l l'} {lε = lε} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
                → Natural-prop Γ lε t
                → Natural-prop Γ lε' t
  Natural-prop≤ f< zeroᵣ = zeroᵣ
  Natural-prop≤ f< (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ neK (Term≤ f< ⊢k) (~-≤ f< k≡k))
  Natural-prop≤ f< (sucᵣ [t]) = sucᵣ (⊩ℕ∷ℕ≤ f< [t])

τ⊩ℕ∷ℕ : ∀ {t l n b nε} {lε : ⊢ₗ l}
           → Γ / lε ⊩ℕ t ∷ℕ
           → Γ / ⊢ₗ• l lε n b nε ⊩ℕ t ∷ℕ
τ⊩ℕ∷ℕ t = ⊩ℕ∷ℕ≤ (λ n b nε → InThere _ nε _ _) t


mutual
  ⊩𝔹∷𝔹≤ :  ∀ {t l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
           → Γ / lε ⊩𝔹 t ∷𝔹
           → Γ / lε' ⊩𝔹 t ∷𝔹
  ⊩𝔹∷𝔹≤ f< (𝔹ₜ n  ([ ⊢t , ⊢n , d ]) n≡n prop) =
    𝔹ₜ n ([ Term≤ f< ⊢t , Term≤ f< ⊢n , RedTerm≤* f< d ]) (≅ₜ-≤ n≡n f<) (Boolean-prop≤ f< prop)
  ⊩𝔹∷𝔹≤ {l' = l'} f< (𝔹ϝ {m = m} tt ft) with decidInLConNat l' m
  ⊩𝔹∷𝔹≤ {l' = l'} f< (𝔹ϝ {m = m} tt ft) | TS.inj₁ (TS.inj₁ inl) = ⊩𝔹∷𝔹≤ (≤ₗ-add _ _ _ f< inl) tt
  ⊩𝔹∷𝔹≤ {l' = l'} f< (𝔹ϝ {m = m} tt ft) | TS.inj₁ (TS.inj₂ inl) = ⊩𝔹∷𝔹≤ (≤ₗ-add _ _ _ f< inl) ft
  ⊩𝔹∷𝔹≤ {l' = l'} f< (𝔹ϝ {m = m} tt ft) | TS.inj₂ notinl =
    𝔹ϝ {mε = notinl} (⊩𝔹∷𝔹≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) tt)
       (⊩𝔹∷𝔹≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) ft)

  Boolean-prop≤ : ∀ {t l l'} {lε = lε} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
                → Boolean-prop Γ lε t
                → Boolean-prop Γ lε' t
  Boolean-prop≤ f< trueᵣ = trueᵣ
  Boolean-prop≤ f< falseᵣ = falseᵣ
  Boolean-prop≤ f< (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ neK (Term≤ f< ⊢k) (~-≤ f< k≡k))


τ⊩𝔹∷𝔹 : ∀ {t l n b nε} {lε : ⊢ₗ l}
           → Γ / lε ⊩𝔹 t ∷𝔹
           → Γ / ⊢ₗ• l lε n b nε ⊩𝔹 t ∷𝔹
τ⊩𝔹∷𝔹 t = ⊩𝔹∷𝔹≤ (λ n b nε → InThere _ nε _ _) t

TermLogNe≤ : ∀ {A t l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
             ([A] : Γ / lε  ⊩ne A)
             ([A'] : Γ / lε'  ⊩ne A)
     → Γ / lε  ⊩ne t ∷ A / [A]
     → Γ / lε' ⊩ne t ∷ A / [A']
TermLogNe≤ f< (ne K D neK K≡K) (ne K' D' neK' K≡K') (neₜ k d (neNfₜ nek ⊢k k≡k))
  with whrDet* ( Red≤* f< (red D) , ne neK) (red D' , ne neK')
TermLogNe≤ f< (ne K D neK K≡K) (ne K' D' neK' K≡K') (neₜ k d (neNfₜ nek ⊢k k≡k))
  | PE.refl =
    neₜ k (wfRedTerm≤* f< d) (neNfₜ nek (Term≤ f< ⊢k) (~-≤ f< k≡k))
TermLogNe≤ {l' = l'} f< (ne K D neK K≡K) (ne K' D' neK' K≡K') (neϝ {m = m} tt ft)
   with decidInLConNat l' m
TermLogNe≤ {l' = l'} f< (ne K D neK K≡K) [A'] (neϝ {[A]t = [A]t} {[A]f = [A]f} tt ft)
  | TS.inj₁ (TS.inj₁ inl) =
  TermLogNe≤ (≤ₗ-add _ _ _ f< inl) [A]t [A'] tt
TermLogNe≤ {l' = l'} f< (ne K D neK K≡K) [A'] (neϝ {[A]t = [A]t} {[A]f = [A]f} tt ft)
  | TS.inj₁ (TS.inj₂ inl) =
  TermLogNe≤  (≤ₗ-add _ _ _ f< inl) [A]f [A'] ft
TermLogNe≤  {l' = l'} f< (ne K D neK K≡K) (ne K' D' neK' K≡K') (neϝ {[A]t = [A]t} {[A]f = [A]f} tt ft)
  | TS.inj₂ notinl =
  neϝ {mε = notinl}
  (TermLogNe≤  (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) [A]t
    (ne K' (τwfRed* D') neK' (~-τ K≡K')) tt)
  (TermLogNe≤  (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< n b inl) _ _) (InHereNat _)) [A]f
    (ne K' (τwfRed* D') neK' (~-τ K≡K')) ft)


TermLog≤₀ : ∀ {A t k l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') [A] [A']
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
     → (μTy [A] PE.≡ 0)
     → (μTy [A']) PE.≡ 0
     → Γ / lε' ⊩⟨ k ⟩ t ∷ A / [A']
TermLog≤₀ f< [A] [A'] t eq₁ eq₂ with goodCasesRefl (TyLog≤ f< [A]) [A']
TermLog≤₀ f< (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uᵣ′ ⁰ 0<1 ⊢Γ') (Uₜ ⊢t t≡t [t]) eq₁ eq₂
  | Uᵥ UA UB UA≡B = Uₜ (Term≤ f< ⊢t) (≅ₜ-≤ t≡t f<) (TyLog≤ f< [t])
TermLog≤₀ f< (ℕᵣ D) (ℕᵣ D') t eq₁ eq₂
  | ℕᵥ ℕA ℕB ℕA≡B = ⊩ℕ∷ℕ≤ f< t
TermLog≤₀ {k = k} f< (𝔹ᵣ D) (𝔹ᵣ D') t eq₁ eq₂
  | 𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B = ⊩𝔹∷𝔹≤ f< t
TermLog≤₀ f< (ne neA@(ne K D neK K≡K)) (ne neA'@(ne K' D' neK' K≡K')) t eq₁ eq₂
  | ne neA′ neA' neA≡A' = TermLogNe≤ f< neA neA' t
TermLog≤₀ f< (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
              t eq₁ eq₂
  | Bᵥ W BA BA' BA≡B
  with whrDet* (red (wfRed≤* f< D) , ?) (red D' , ?)
TermLog≤₀ {k = k} f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                    (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
                    (⊢t , t≡t , [t≡t] , [t]) eq₁ eq₂
  | Bᵥ BΠ BA BA' BA≡B
  | PE.refl =
   Term≤ f< ⊢t , (≅ₜ-≤ t≡t f< ,
     ((λ {m} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} → ? ) , --[t≡t] {_} {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}) ,
       λ {m} {ρ} {Δ} {a} {l'} {≤ε} {lε'} → ?)) --[t] {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}))
TermLog≤₀ {k = k} f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                    (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
                    (p , d , prodp , p≡p , [p₁] , [p₂]) eq₁ eq₂
  | Bᵥ BΣ BA BA' BA≡B
  | PE.refl =
  p , (wfRedTerm≤* f< d , (prodp , (≅ₜ-≤ p≡p f< , ? , ?)))
TermLog≤₀ {k = k} f< (emb 0<1 [A]) [A'] t () eq₂
TermLog≤₀ {k = k} f< [A] (emb 0<1 [A']) t eq₁ ()
TermLog≤₀ {k = k} f< (ϝᵣ mε tA fA) [A'] t () eq₂
TermLog≤₀ {k = k} f< [A] (ϝᵣ mε tA' fA') t eq₁ ()


TermLog≤₁ : ∀ {A t k k′ l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') [A] [A']
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
     → Γ / lε' ⊩⟨ k′ ⟩ t ∷ A / [A']
TermLog≤₁ f< [A] [A'] t with goodCasesRefl (TyLog≤ f< [A]) [A']
TermLog≤₁ f< (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uᵣ′ ⁰ 0<1 ⊢Γ') (Uₜ ⊢t t≡t [t])
  | Uᵥ UA UB UA≡B = Uₜ (Term≤ f< ⊢t) (≅ₜ-≤ t≡t f<) (TyLog≤ f< [t])
TermLog≤₁ f< (ℕᵣ D) (ℕᵣ D') t
  | ℕᵥ ℕA ℕB ℕA≡B = ⊩ℕ∷ℕ≤ f< t
TermLog≤₁ {k = k} f< (𝔹ᵣ D) (𝔹ᵣ D') t
  | 𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B = ⊩𝔹∷𝔹≤ f< t
TermLog≤₁ f< (ne neA@(ne K D neK K≡K)) (ne neA'@(ne K' D' neK' K≡K')) t
  | ne neA′ neA' neA≡A' = TermLogNe≤ f< neA neA' t
TermLog≤₁ f< (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
              t
  | Bᵥ W BA BA' BA≡B
  with whrDet* (red (wfRed≤* f< D) , ?) (red D' , ?)
TermLog≤₁ {k = k} f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                    (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
                    (⊢t , t≡t , [t≡t] , [t])
  | Bᵥ BΠ BA BA' BA≡B
  | PE.refl =
   Term≤ f< ⊢t , (≅ₜ-≤ t≡t f< ,
     ((λ {m} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} → ? ) , --[t≡t] {_} {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}) ,
       λ {m} {ρ} {Δ} {a} {l'} {≤ε} {lε'} → ?)) --[t] {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}))
TermLog≤₁ {k = k} f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                    (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
                    (p , d , prodp , p≡p , [p₁] , [p₂])
  | Bᵥ BΣ BA BA' BA≡B
  | PE.refl =
  p , (wfRedTerm≤* f< d , (prodp , (≅ₜ-≤ p≡p f< , ? , ?)))
TermLog≤₁ {k = k} f< (emb 0<1 [A]) [A'] t
  | emb⁰¹ Shp = TermLog≤₁ f< [A] [A'] t
TermLog≤₁ {k = k} f< [A] (emb 0<1 [A']) t
  | emb¹⁰ Shp = TermLog≤₁ f< [A] [A'] t
TermLog≤₁ {k = k} {l' = l'} f< (ϝᵣ {m = m} mε tA fA) [A'] t
  | Shp with decidInLConNat l' m
TermLog≤₁ {k = k} {l' = l'} f< (ϝᵣ {m = m} mε tA fA) [A'] t
  | Shp | TS.inj₁ (TS.inj₁ inl) = ?
TermLog≤₁ {k = k} {l' = l'} f< (ϝᵣ {m = m} mε tA fA) [A'] t
  | Shp | TS.inj₁ (TS.inj₂ inl) = ?
TermLog≤₁ {k = k} {l' = l'} f< (ϝᵣ {m = m} mε tA fA) [A'] t
  | Shp
  | TS.inj₂ notinl = {!!}
TermLog≤₁ {k = k} f< [A] (ϝᵣ mε tA' fA') t
  | Shp = ?




irrelTerm : ∀ {A t k k′}
      (p : Γ / lε ⊩⟨ k ⟩ A) 
      (q : Γ / lε ⊩⟨ k′ ⟩ A)
      → Γ / lε ⊩⟨ k ⟩ t ∷ A / p
      → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
irrelTerm p q t = {!!}
      

ϝTermLogHelper :
  ∀ (ϝL : ∀ {A t k k′ k″ n nε} [A]
     (p : Γ / ⊢ₗ• l lε n Btrue nε   ⊩⟨ k′ ⟩ A) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ A)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ A / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ A / q
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A])
  {F G t k k′ k″ m} {mε : NotInLConNat m l}
  ([tF] : ∀ {m' : Nat} {l' : LCon}
         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
         {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
           ρ Wk.∷ Δ ⊆ Γ →
           ⊢ Δ / lε' → Δ / lε' ⊩⟨ k′ ⟩ (wk ρ F))
  ([tG] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
         {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
         (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
         ([tF] {≤ε = ≤ε} [ρ] ⊢Δ) →
         (k′ LogRel./ logRelRec k′ ⊩¹ Δ) lε'
         (subst (consSubst var a) (wk (lift ρ) G)))
  ([tt] : ∀ {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
         {lε' : ⊢ₗ l'}
         ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
         ([a] : (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
            ([tF] {≤ε = ≤ε} [ρ] ⊢Δ)) →
         (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' /
           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
         (subst (consSubst var a) (wk (lift ρ) G)) ([tG] [ρ] ⊢Δ [a]))
  ([fF] : ∀ {m' : Nat} {l' : LCon}
         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
         {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
           ρ Wk.∷ Δ ⊆ Γ →
           ⊢ Δ / lε' → Δ / lε' ⊩⟨ k″ ⟩ (wk ρ F))
  ([fG] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
         {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
         (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
         ([fF] {≤ε = ≤ε} [ρ] ⊢Δ) →
         (k″ LogRel./ logRelRec k″ ⊩¹ Δ) lε'
         (subst (consSubst var a) (wk (lift ρ) G)))
  ([ft] : ∀ {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
         {lε' : ⊢ₗ l'}
         ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
         ([a] : (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
            ([fF] {≤ε = ≤ε} [ρ] ⊢Δ)) →
         (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' /
           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
         (subst (consSubst var a) (wk (lift ρ) G)) ([fG] {≤ε = ≤ε} [ρ] ⊢Δ [a]))
  ([F] : ∀ {m' : Nat} {l' : LCon}
         {≤ε : l ≤ₗ l'}
         {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
           ρ Wk.∷ Δ ⊆ Γ →
           ⊢ Δ / lε' → Δ / lε' ⊩⟨ k ⟩ (wk ρ F))
  ([G] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : l ≤ₗ l'}
         {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
         (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' / a) (wk ρ F)
         ([F] {≤ε = ≤ε} [ρ] ⊢Δ) →
         (k LogRel./ logRelRec k ⊩¹ Δ) lε'
         (subst (consSubst var a) (wk (lift ρ) G)))     
       {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
         {a : Term m'} {l' : LCon}
         {≤ε : l ≤ₗ l'}
         {lε' : ⊢ₗ l'}
         ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
         ([a] : (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' / a) (wk ρ F)
            ([F] {≤ε = ≤ε} [ρ] ⊢Δ)) →
         (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' /
           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
         (subst (consSubst var a) (wk (lift ρ) G)) ([G] {≤ε = ≤ε} [ρ] ⊢Δ [a])
ϝTermLogHelper ϝL {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
  with decidInLConNat l' m
ϝTermLogHelper ϝL {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
  | TS.inj₁ (TS.inj₁ inl) = let [T] = [tt] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a])
                              in irrelTerm ([tG] [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a])) ([G] [ρ] ⊢Δ [a]) [T]
ϝTermLogHelper ϝL {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
  | TS.inj₁ (TS.inj₂ inl) = let [T] = [ft] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a])
                              in irrelTerm ([fG] [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a])) ([G] [ρ] ⊢Δ [a]) [T]
ϝTermLogHelper ϝL {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
  | TS.inj₂ notinl =
  let [tT] = [tt] {≤ε = {!!}} [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a])
      [fT] = [ft] {≤ε = {!!}} [ρ] ⊢Δ (irrelTerm ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a])
  in
    {!!}

ϝTermLog : ∀ {A t k k′ k″ n nε} [A]
     (p : Γ / ⊢ₗ• l lε n Btrue nε   ⊩⟨ k′ ⟩ A) 
     (q : Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ A)
     → Γ / ⊢ₗ• l lε n Btrue nε  ⊩⟨ k′ ⟩ t ∷ A / p
     → Γ / ⊢ₗ• l lε n Bfalse nε ⊩⟨ k″ ⟩ t ∷ A / q
     → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
ϝTermLog {k = k} (Uᵣ UA) p q tt ft = ϝU {k = k} (μTy p + μTy q) UA p q tt ft (≤-refl _)
ϝTermLog {k = k} (𝔹ᵣ 𝔹A) p q tt ft = ϝ𝔹 {k = k} 𝔹A p q tt ft
ϝTermLog {k = k} (ℕᵣ ℕA) p q tt ft = ϝℕ {k = k} ℕA p q tt ft
ϝTermLog {k = k} (ne neA) p q tt ft = ϝNe {k = k} neA p q tt ft
ϝTermLog (emb 0<1 [A]) p q tt ft = ϝTermLog [A] p q tt ft
ϝTermLog {k = k} (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
  with goodCasesRefl {k = k} (Bᵣ′ W F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
       (λ {m} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext) p
  with goodCasesRefl {k = k} (Bᵣ′ W F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
       (λ {m} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext) q
ϝTermLog BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
         (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
         (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
         (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft])
 | Bᵥ BΠ BA′ tBB tBA≡B
 | Bᵥ BΠ BA″ fBB fBA≡B
 with whrDet* (τRed* (red D) , Πₙ) (red tD , Πₙ)
 with whrDet* (τRed* (red D) , Πₙ) (red fD , Πₙ)
ϝTermLog {n = n} BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
         (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
         (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
         (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft])
 | Bᵥ BΠ BA′ tBB tBA≡B
 | Bᵥ BΠ BA″ fBB fBA≡B
 | PE.refl | PE.refl = ϝⱼ t⊢t f⊢t , (≅ₜ-ϝ tt≡t ft≡t , ((λ {m} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} [a] [b] a≡b → {!!}) ,
           λ {m} {ρ} {Δ} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] → {!!}))
           -- ϝTermLog _ _ _ ([tt] {_} {_} {_} {_} {_} {λ n b nε → ≤ε n b {!!}} [ρ] (Con≤ (λ n b nε → nε) ⊢Δ) {!!}) {!!}))
ϝTermLog BA@(Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
 | Bᵥ BΣ BA′ tBB tBA≡B
 | Bᵥ BΣ BA″ fBB fBA≡B = {!!}
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p (emb 0<1 q) tt ft
 | Bᵥ W BA′ tBB tBA≡B
 | emb¹⁰ fA = ϝTermLog BA p q tt ft
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
 | Bᵥ W BA′ tBB tBA≡B
 | ϝᵣ-r (Bᵣ W BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = {!!}
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb 0<1 p) q tt ft
 | emb¹⁰ [A] | _ = ϝTermLog BA p q tt ft
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
 | ϝᵣ-r (Bᵣ W BA′) tBAt tBAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
 | Bᵥ W BA″ fBB fBA≡B = {!!}
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p (emb 0<1 q) tt ft
 | ϝᵣ-r (Bᵣ W BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB
 | emb¹⁰ [A] = ϝTermLog BA p q tt ft
ϝTermLog BA@(Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
 | ϝᵣ-r (Bᵣ W BA′) tBAt tBAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
 | ϝᵣ-r (Bᵣ W BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = {!!}
ϝTermLog (ϝᵣ mε [A] [A]₁) p q tt ft = {!!}
