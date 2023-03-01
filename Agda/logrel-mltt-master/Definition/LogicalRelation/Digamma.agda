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


Not : Bbool → Bbool
Not Btrue = Bfalse
Not Bfalse = Btrue




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


mutual 
  TermLog≤ : ∀ {A t k l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (f< : l ≤ₗ l') [A]
           → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
           → Γ / lε' ⊩⟨ k ⟩ t ∷ A / TyLog≤ f< [A]
  TermLog≤ {k = k} f< (Uᵣ (Uᵣ _ 0<1 ⊢Γ)) (Uₜ ⊢t t≡t [t]) = Uₜ (Term≤ f< ⊢t) (≅ₜ-≤ t≡t f<) (TyLog≤ f< [t])
  TermLog≤ {k = k} f< (𝔹ᵣ D) t =  ⊩𝔹∷𝔹≤ f< t
  TermLog≤ {k = k} f< (ℕᵣ D) t = ⊩ℕ∷ℕ≤ f< t
  TermLog≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) t with decidInLConNat l' m
  TermLog≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) (tt , ft)
    | TS.inj₁ (TS.inj₁ inl') = TermLog≤ (≤ₗ-add _ _ _ f< inl') tA tt
  TermLog≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) (tt , ft)
    | TS.inj₁ (TS.inj₂ inl') = TermLog≤ (≤ₗ-add _ _ _ f< inl') fA ft
  TermLog≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) (tt , ft)
    | TS.inj₂ notinl' = TermLog≤ (≤ₗ-add-b f<) tA tt , TermLog≤ (≤ₗ-add-b f<) fA ft
  TermLog≤ f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (⊢t , t≡t , [t≡t] , [t]) =
    Term≤ f< ⊢t , (≅ₜ-≤ t≡t f< ,
                  ((λ {m} {ρ} {Δ} {a} {b} {l''} {≤ε} → [t≡t] {≤ε = ≤ₗ-• f< ≤ε}) ,
                    λ {m} {ρ} {Δ} {a} {l''} {≤ε} → [t] {≤ε = ≤ₗ-• f< ≤ε}))
  TermLog≤ f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (p , t⇒p , prodp , p≡p , [fst] , [snd]) =
    p , (wfRedTerm≤* f< t⇒p , (prodp , (≅ₜ-≤ p≡p f< , (irrelevanceTerm (TyLog≤ f< ([F] Wk.id (wf ⊢F))) ([F] Wk.id (wf (Ty≤ f< ⊢F))) (TermLog≤ f< ([F] _ (wf ⊢F)) [fst]) ,
        irrelevanceTerm (TyLog≤ f< ([G] Wk.id (wf ⊢F) [fst])) ([G] Wk.id (wf (Ty≤ f< ⊢F)) _) (TermLog≤ f< ([G] Wk.id (wf ⊢F) [fst]) [snd])))))
  TermLog≤ f< (ne neA) t = TermLogNe≤ f< neA _ t
  TermLog≤ f< (emb 0<1 [A]) t = TermLog≤ f< [A] t
  

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


  irrelevanceTermT : ∀ {A t k k′} {p : Γ / lε ⊩⟨ k ⟩ A} {q : Γ / lε ⊩⟨ k′ ⟩ A} {A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ A / p}
                        → ShapeView Γ k k′ A A p q A≡B
                        → Γ / lε ⊩⟨ k ⟩ t ∷ A / p
                        → Γ / lε ⊩⟨ k′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′ A≡B) t = t
  irrelevanceTermT (𝔹ᵥ D D′ A≡B) t = t
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁) A≡B) (Uₜ ⊢t t≡t [t]) = Uₜ ⊢t t≡t [t]
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                             (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
                                             (Σₜ p d pProd p≅p [fst] [snd]) =
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
  irrelevanceTermT {Γ = Γ} {lε = lε} {t = t} (Bᵥ BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                      (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) A≡B)
                   (Πₜ ⊢f f≡f [f] [f]₁) =
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
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) t
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁) A≡B) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁) A≡B) (neϝ tk fk)
    | PE.refl  = neϝ tk fk
  irrelevanceTermT {q = q} (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t
  irrelevanceTermT (ϝᵣ-l [A] [B] [A]t [A]f [B]t [B]f tA≡B fA≡B tAB fAB) t = {!!}
  irrelevanceTermT {q = q} (ϝᵣ-r [A] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) t =
                    {!!} , {!!}

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
  irrelevanceEqTermT (ϝᵣ-r [A] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) t =  {!!} , {!!} 


-- AllIncl≤ : ∀ {A t k k′ l l'} {m b} {mε : NotInLConNat m l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (f< : l ≤ₗ addₗ m b l') [A]
--            (tA : Γ / ⊢ₗ• l' lε' m b mε ⊩⟨ k′ ⟩ A)
--           → (Γ / lε ⊩⟨ k ⟩ t ∷ A / [A] → Γ / ⊢ₗ• l' lε' m b mε ⊩⟨ k′ ⟩ t ∷ A / tA) ×
--             (∀ {k″ k‴ : TypeLevel} fA [A']
--                → Γ / ⊢ₗ• l' lε' m b  mε ⊩⟨ k′ ⟩ t ∷ A / tA
--                → Γ / ⊢ₗ• l' lε' m (Not b) mε ⊩⟨ k″ ⟩ t ∷ A / fA
--                → Γ / lε' ⊩⟨ k‴ ⟩ t ∷ A / [A'])
-- AllIncl≤ {k = k} f< (Uᵣ D) tA = {!!} , {!!}
-- AllIncl≤ {k = k} f< (𝔹ᵣ D) tA = {!!} , {!!}
-- AllIncl≤ {k = k} f< (ℕᵣ D) tA = {!!} , {!!}
-- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA' with decidInLConNat l' m
-- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA'
--   | TS.inj₁ (TS.inj₁ inl') = {!!}
-- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA'
--   | TS.inj₁ (TS.inj₂ inl') = {!!}
-- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA'@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   | TS.inj₂ notinl' = 
--   let (ttaux , taux) = AllIncl≤ {mε = {!!}} (≤ₗ-add-b f<) tA (τTyLog tA')
--       (ffaux , faux) = AllIncl≤ (≤ₗ-add-b f<) fA (τTyLog tA')
--    in (λ ((tt , ft)) → taux (τTyLog tA') tA' (ttaux tt) (ffaux ft)) ,
--       λ fA [A'] tt ft → {!!}
-- AllIncl≤ {l' = l'} {m = m} {b = Btrue} f< (ϝᵣ {m = m'} mε tA fA) tA'
--   | TS.inj₂ notinl' =
--   let (ttaux , taux) = AllIncl≤ (≤ₗ-add-b f<) tA (τTyLog tA')
--       (ffaux , faux) = AllIncl≤ (≤ₗ-add-b f<) fA (τTyLog tA')
--    in (λ ((tt , ft)) → taux (τTyLog tA') tA' (ttaux tt) (ffaux ft)) ,
--       λ fA [A'] tt ft → {!!}
-- AllIncl≤ {l' = l'} {m = m} {b = Bfalse} f< (ϝᵣ {m = m'} mε tA fA) tA'
--   | TS.inj₂ notinl' =
--   let (ttaux , taux) = AllIncl≤ (≤ₗ-add-b f<) tA (τTyLog tA')
--       (ffaux , faux) = AllIncl≤ (≤ₗ-add-b f<) fA (τTyLog tA')
--    in      (λ ((tt , ft)) → taux (τTyLog tA') tA' (ttaux tt) (ffaux ft)) , {!!}
-- AllIncl≤ f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) tA  = {!!} , {!!}
-- AllIncl≤ f< [A] tA = {!!} , {!!}




-- -- AllIncl≤ : ∀ {A t k k′ k″ l l'} {m} {mε : NotInLConNat m l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (f< : l ≤ₗ l') [A]
-- --            (tA : Γ / ⊢ₗ• l' lε' m Btrue mε ⊩⟨ k′ ⟩ A)
-- --            (fA : Γ / ⊢ₗ• l' lε' m Bfalse mε ⊩⟨ k″ ⟩ A)
-- --           → ((Γ / lε ⊩⟨ k ⟩ t ∷ A / [A] → Γ / ⊢ₗ• l' lε' m Btrue  mε ⊩⟨ k′ ⟩ t ∷ A / tA) ×
-- --             (Γ / lε ⊩⟨ k ⟩ t ∷ A / [A] → Γ / ⊢ₗ• l' lε' m Bfalse mε ⊩⟨ k″ ⟩ t ∷ A / fA)) ×
-- --             (∀ {k‴ : TypeLevel} [A']
-- --                → Γ / ⊢ₗ• l' lε' m Btrue  mε ⊩⟨ k′ ⟩ t ∷ A / tA
-- --                → Γ / ⊢ₗ• l' lε' m Bfalse mε ⊩⟨ k″ ⟩ t ∷ A / fA
-- --                → Γ / lε' ⊩⟨ k‴ ⟩ t ∷ A / [A'])
-- -- AllIncl≤ {k = k} f< (Uᵣ D) tA fA = {!!} , {!!}
-- -- AllIncl≤ {k = k} f< (𝔹ᵣ D) tA fA = {!!} , {!!}
-- -- AllIncl≤ {k = k} f< (ℕᵣ D) tA fA = {!!} , {!!}
-- -- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA' fA' with decidInLConNat l' m
-- -- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA' fA'
-- --   | TS.inj₁ (TS.inj₁ inl') = {!!}
-- -- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) tA' fA'
-- --   | TS.inj₁ (TS.inj₂ inl') = {!!}
-- -- AllIncl≤ {l' = l'} f< (ϝᵣ {m = m} mε tA fA) (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) fA'
-- --   | TS.inj₂ notinl' = {!!}
-- -- AllIncl≤ {l' = l'} {m = m} f< (ϝᵣ {m = m'} mε tA fA) tA' fA'
-- --   | TS.inj₂ notinl' =
-- --   let ((ttaux , tfaux) , taux) = AllIncl≤ {!!} tA (τTyLog tA') (τTyLog tA')
-- --       ((ftaux , ffaux) , faux) = AllIncl≤ {!!} fA (τTyLog fA') (τTyLog fA')
-- --   in ((λ (tt , ft) → taux tA' (ttaux tt) (tfaux tt)) ,
-- --      λ (tt , ft) → faux fA' (ftaux ft) (ffaux ft)) ,
-- --          {!!}
-- -- AllIncl≤ f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) tA fA  = {!!} , {!!}
-- -- AllIncl≤ f< [A] tA fA  = {!!} , {!!}


-- -- -- mutual

-- -- --   -- ConvLog≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') {k k′ A B}
-- -- --   --            → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
-- -- --   --            → ([A'] :  Γ / lε' ⊩⟨ k′ ⟩ A)
-- -- --   --            → Γ / lε ⊩⟨ k ⟩ A ≡ B / [A]
-- -- --   --            → Γ / lε' ⊩⟨ k′ ⟩ A ≡ B / [A']
-- -- --   -- ConvLog≤ {l' = l'} f< [A] [A'] (⊩¹≡ϝ {m = m} _ tA fA tA≡B fA≡B) with decidInLConNat l' m
-- -- --   -- ConvLog≤ {l' = l'} f< [A] [A'] (⊩¹≡ϝ {m = m} _ tA fA tA≡B fA≡B)
-- -- --   --   | TS.inj₁ (TS.inj₁ inl) = {!!}
-- -- --   -- ConvLog≤ {l' = l'} f< [A] [A'] (⊩¹≡ϝ {m = m} _ tA fA tA≡B fA≡B)
-- -- --   --   | TS.inj₁ (TS.inj₂ inl) = {!!}
-- -- --   -- ConvLog≤ {l' = l'} f< [A] [A'] (⊩¹≡ϝ {m = m} _ tA fA tA≡B fA≡B)
-- -- --   --   | TS.inj₂ notinl' =
-- -- --   --     ⊩¹≡ϝ {mε = notinl'} [A'] (τTyLog [A']) (τTyLog [A'])
-- -- --   --          (ConvLog≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) tA _ tA≡B)
-- -- --   --          (ConvLog≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) fA _ fA≡B)
-- -- --   -- ConvLog≤ ≤ε (Uᵣ UA) [A'] (⊩¹≡U .UA x) = {!!}
-- -- --   -- ConvLog≤ ≤ε (ℕᵣ D) [A'] (⊩¹≡ℕ .D x) = {!!}
-- -- --   -- ConvLog≤ ≤ε (𝔹ᵣ D) [A'] (⊩¹≡𝔹 .D x) = {!!}
-- -- --   -- ConvLog≤ ≤ε (ne neA) [A'] (⊩¹≡ne .neA x) = {!!}
-- -- --   -- ConvLog≤ ≤ε (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --             (Bᵣ BΠ [A']@(Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
-- -- --   --             (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]))
-- -- --   --             with whrDet* (Red≤* ≤ε (red D) , Πₙ) (red D' , Πₙ)
-- -- --   -- ConvLog≤ ≤ε (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --             (Bᵣ BΠ [A']@(Bᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
-- -- --   --             (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]))
-- -- --   --             | PE.refl =
-- -- --   --             ⊩¹≡B BΠ [A'] (B₌ F′ G′ (Red≤* ≤ε D′) (≅-≤ ≤ε A≡B)
-- -- --   --                              (λ {m} {ρ} {Δ} {l'} {≤ε'} {lε'} [ρ] ⊢Δ →
-- -- --   --                                ConvLog≤ (≤ₗ-id _) _ ([F'] [ρ] ⊢Δ) ([F≡F′] {≤ε = ≤ₗ-• ≤ε ≤ε'} [ρ] ⊢Δ))
-- -- --   --                                (λ {m} {ρ} {Δ} {a} {l'} {≤ε'} {lε'} [ρ] ⊢Δ [a] →
-- -- --   --                                  ConvLog≤ (≤ₗ-id _) _ ([G'] [ρ] ⊢Δ [a])
-- -- --   --                                    ([G≡G′] [ρ] ⊢Δ (TermLog≤₁ _ (≤ₗ-id _) ([F'] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a] (≤-refl _)))))
-- -- --   -- ConvLog≤ ≤ε (emb j< [A]) [A'] (⊩¹≡emb .j< .[A] x) = {!!}
-- -- --   -- ConvLog≤ ≤ε [A] [A'] A≡B = {!!}
  

-- -- --   -- TermLog≤₀ : ∀ {A t k l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') [A] [A']
-- -- --   --           → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
-- -- --   --           → (μTy [A] PE.≡ 0)
-- -- --   --           → (μTy [A']) PE.≡ 0
-- -- --   --           → Γ / lε' ⊩⟨ k ⟩ t ∷ A / [A']
-- -- --   -- TermLog≤₀ f< [A] [A'] t eq₁ eq₂ with goodCasesRefl (TyLog≤ f< [A]) [A']
-- -- --   -- TermLog≤₀ f< (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uᵣ′ ⁰ 0<1 ⊢Γ') (Uₜ ⊢t t≡t [t]) eq₁ eq₂
-- -- --   --   | Uᵥ UA UB UA≡B = Uₜ (Term≤ f< ⊢t) (≅ₜ-≤ t≡t f<) (TyLog≤ f< [t])
-- -- --   -- TermLog≤₀ f< (ℕᵣ D) (ℕᵣ D') t eq₁ eq₂
-- -- --   --   | ℕᵥ ℕA ℕB ℕA≡B = ⊩ℕ∷ℕ≤ f< t
-- -- --   -- TermLog≤₀ {k = k} f< (𝔹ᵣ D) (𝔹ᵣ D') t eq₁ eq₂
-- -- --   --   | 𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B = ⊩𝔹∷𝔹≤ f< t
-- -- --   -- TermLog≤₀ f< (ne neA@(ne K D neK K≡K)) (ne neA'@(ne K' D' neK' K≡K')) t eq₁ eq₂
-- -- --   --   | ne neA′ neA' neA≡A' = TermLogNe≤ f< neA neA' t
-- -- --   -- TermLog≤₀ f< (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --              (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --   --              t eq₁ eq₂
-- -- --   --           | Bᵥ W BA BA' BA≡B
-- -- --   --           with whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ⟦ W ⟧ₙ)
-- -- --   -- TermLog≤₀ {k = k} f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --                      (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --   --                      (⊢t , t≡t , [t≡t] , [t]) eq₁ eq₂
-- -- --   --           | Bᵥ BΠ BA BA' BA≡B
-- -- --   --           | PE.refl =
-- -- --   --           Term≤ f< ⊢t , (≅ₜ-≤ t≡t f< ,
-- -- --   --           ((λ {m} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} → {!!} ) , --[t≡t] {_} {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}) ,
-- -- --   --           λ {m} {ρ} {Δ} {a} {l'} {≤ε} {lε'} → {!!})) --[t] {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}))
-- -- --   -- TermLog≤₀ {k = k} f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --                      (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --   --                      (p , d , prodp , p≡p , [p₁] , [p₂]) eq₁ eq₂
-- -- --   --           | Bᵥ BΣ BA BA' BA≡B
-- -- --   --           | PE.refl =
-- -- --   --           p , (wfRedTerm≤* f< d , (prodp , (≅ₜ-≤ p≡p f< , {!!} , {!!})))
-- -- --   -- TermLog≤₀ {k = k} f< (emb 0<1 [A]) [A'] t () eq₂
-- -- --   --   | _
-- -- --   -- TermLog≤₀ {k = k} f< [A] (emb 0<1 [A']) t eq₁ ()
-- -- --   --   | _
-- -- --   -- TermLog≤₀ {k = k} f< (ϝᵣ mε tA fA) [A'] t () eq₂
-- -- --   --   | _
-- -- --   -- TermLog≤₀ {k = k} f< [A] (ϝᵣ mε tA' fA') t eq₁ ()
-- -- --   --   | _
  
  
-- -- --   TermLog≤₁ : ∀ {A t k k′ l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (N : Nat) (≤ε : l ≤ₗ l') [A] [A']
-- -- --             → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
-- -- --             → (((μTy [A]) + (μTy [A'])) ≤ N) 
-- -- --             → Γ / lε' ⊩⟨ k′ ⟩ t ∷ A / [A']
-- -- --   TermLog≤₁ N f< [A] [A'] t N< with goodCasesRefl (TyLog≤ f< [A]) [A']
-- -- --   TermLog≤₁ N f< (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uᵣ′ ⁰ 0<1 ⊢Γ') (Uₜ ⊢t t≡t [t]) N<
-- -- --     | Uᵥ UA UB UA≡B = Uₜ (Term≤ f< ⊢t) (≅ₜ-≤ t≡t f<) (TyLog≤ f< [t])
-- -- --   TermLog≤₁ N f< (ℕᵣ D) (ℕᵣ D') t N<
-- -- --     | ℕᵥ ℕA ℕB ℕA≡B = ⊩ℕ∷ℕ≤ f< t
-- -- --   TermLog≤₁ {k = k} N f< (𝔹ᵣ D) (𝔹ᵣ D') t N<
-- -- --     | 𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B = ⊩𝔹∷𝔹≤ f< t
-- -- --   TermLog≤₁ N f< (ne neA@(ne K D neK K≡K)) (ne neA'@(ne K' D' neK' K≡K')) t N<
-- -- --     | ne neA′ neA' neA≡A' = TermLogNe≤ f< neA neA' t
-- -- --   TermLog≤₁ N f< (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --                (Bᵣ′ W F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --                t N<
-- -- --             | Bᵥ W BA BA' BA≡B
-- -- --             with whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ⟦ W ⟧ₙ)
-- -- --   TermLog≤₁ {k = k} N f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --                        (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --                        (⊢t , t≡t , [t≡t] , [t]) N<
-- -- --             | Bᵥ BΠ BA BA' BA≡B
-- -- --             | PE.refl =
-- -- --             Term≤ f< ⊢t , (≅ₜ-≤ t≡t f< ,
-- -- --             ((λ {m} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} → {!!} ) , --[t≡t] {_} {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε}) ,
-- -- --             λ {m} {ρ} {Δ} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a]
-- -- --               → let [ttt] = [t] {_} {_} {_} {_} {_} {≤ₗ-• f< ≤ε} [ρ] ⊢Δ (TermLog≤₁ _ (≤ₗ-id _) ([F'] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a] (≤-refl _))
-- -- --                 in TermLog≤₁ _ (≤ₗ-id _) ([G] [ρ] ⊢Δ (TermLog≤₁ _ (≤ₗ-id l') ([F'] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a] (≤-refl _)))
-- -- --                 ([G'] [ρ] ⊢Δ [a]) [ttt] (≤-refl _)))
-- -- --   TermLog≤₁ {k = k} N f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --                        (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')
-- -- --                        (p , d , prodp , p≡p , [p₁] , [p₂]) N<
-- -- --             | Bᵥ BΣ BA BA' BA≡B
-- -- --             | PE.refl =
-- -- --             p , (wfRedTerm≤* f< d , (prodp , (≅ₜ-≤ p≡p f< , {!!} , {!!})))
-- -- --   TermLog≤₁ {k = k} (1+ N) f< (emb 0<1 [A]) [A'] t (≤-s N<)
-- -- --     | emb⁰¹ Shp = TermLog≤₁ N f< [A] [A'] t N<
-- -- --   TermLog≤₁ {k = k} N f< [A] (emb 0<1 [A']) t N<
-- -- --     | Shp 
-- -- --     with ≤-trans (≤₊-s-swap _ _) N<
-- -- --   TermLog≤₁ {k = k} (1+ N) f< [A] (emb 0<1 [A']) t N<
-- -- --     | Shp | ≤-s K< = {!!} -- TermLog≤₁ N f< [A] [A'] t K<
-- -- --   TermLog≤₁ {k = k} {l' = l'} N f< (ϝᵣ {m = m} mε tA fA) [A'] t N<
-- -- --     | Shp with decidInLConNat l' m
-- -- --   TermLog≤₁ (1+ N) f< (ϝᵣ {m = m} mε tA fA) [A'] (tt , ft) (≤-s N<)
-- -- --     | Shp | TS.inj₁ (TS.inj₁ inl) =
-- -- --     TermLog≤₁ N (≤ₗ-add _ _ _ f< inl) tA [A'] tt (≤-trans (≤₊-trans-l (μTy [A']) (≤₊-l _ _)) N<)
-- -- --   TermLog≤₁ (1+ N) f< (ϝᵣ {m = m} mε tA fA) [A'] (tt , ft) (≤-s N<)
-- -- --     | Shp | TS.inj₁ (TS.inj₂ inl) =
-- -- --     TermLog≤₁ N (≤ₗ-add _ _ _ f< inl) fA [A'] ft (≤-trans (≤₊-trans-l (μTy [A']) (≤₊-r _ _)) N<)
-- -- --   TermLog≤₁ {t = t} {k = k} {k′ = k′} (1+ N) f< (ϝᵣ {m = m} mε tA fA) [A']@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (tt , ft) (≤-s N<)
-- -- --     | Shp
-- -- --     | TS.inj₂ notinl = let tA' = Bᵣ′ BΠ F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) (λ {_} {_} {≤ε} → [F] {≤ε = ≤ₗ-• (≤ₗ-add-r (≤ₗ-id _)) ≤ε}) [G] G-ext
-- -- --                            fA' = Bᵣ′ BΠ F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) (λ {_} {_} {≤ε} → [F] {≤ε = ≤ₗ-• (≤ₗ-add-r (≤ₗ-id _)) ≤ε}) [G] G-ext
-- -- --                            (t⊢t , tt≡t , [tt≡t] , [tt]) = TermLog≤₁ N (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) tA tA' tt {!!}
-- -- --                            (f⊢t , ft≡t , [ft≡t] , [ft]) = TermLog≤₁ N (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) fA fA' ft {!!}
-- -- --                        in ϝⱼ t⊢t f⊢t , (≅ₜ-ϝ tt≡t ft≡t , ((λ {_} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε' = lε''} [a] [b] a≡b → {!!}) ,
-- -- --                                        λ {_} {ρ} {Δ} {a} {l'} {≤ε} {lε' = lε''} [ρ] ⊢Δ [a] →
-- -- --                                          let Helper : (InLConNat m Btrue l' TS.⊎ InLConNat m Bfalse l') TS.⊎ NotInLConNat m l' →
-- -- --                                                       (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε'' / gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --                                                           (subst (consSubst var a) (wk (lift ρ) G)) ([G] {≤ε = ≤ε} [ρ] ⊢Δ [a])
-- -- --                                              Helper =
-- -- --                                                (λ {(TS.inj₁ (TS.inj₁ inl)) → let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([F] {≤ε = {!!}} [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --                                                                                  [T] = [tt] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --                                                                              in {!!} ; --TermLog≤₁ _ (≤ₗ-id _) ([G] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --                                                    (TS.inj₁ (TS.inj₂ inl)) → {!!} ; --let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --                                                                                     -- [T] = [ft] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --                                                                                   -- in TermLog≤₁ _ (≤ₗ-id _) ([fG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --                                                   (TS.inj₂ notinl) → let ⊢Δ' = λ {b} → (τCon _ _ b notinl ⊢Δ)
-- -- --                                                                          [ta'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ)
-- -- --                                                                                            ([F] {≤ε = ≤ₗ-• ≤ε (≤ₗ-add-r (≤ₗ-id _))} [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --                                                                          [fa'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ)
-- -- --                                                                                            ([F] {≤ε = ≤ₗ-• ≤ε (≤ₗ-add-r (≤ₗ-id _))} [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --                                                                          [tT] = [tt] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] ⊢Δ' [ta']
-- -- --                                                                          [fT] = [ft] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] ⊢Δ' [fa']
-- -- --                                                                      in {!!} }) -- ϝTermLog ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ' [ta']) ([G] [ρ] ⊢Δ' [fa']) [tT] [fT]})
-- -- --                                                in Helper (decidInLConNat l' m))) -- ϝTermLog [A'] (τTyLog [A']) (τTyLog [A']) ttt fft
-- -- --   TermLog≤₁ (1+ N) f< (ϝᵣ {m = m} mε tA fA) [A'] (tt , ft) (≤-s N<)
-- -- --     | Shp
-- -- --     | TS.inj₂ notinl = -- let ttt = TermLog≤₁ N (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) tA (τTyLog [A']) tt {!!}
-- -- --                        --    fft = TermLog≤₁ N (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) fA (τTyLog [A']) ft {!!}
-- -- --                        {!!} --   in {!!} -- ϝTermLog [A'] (τTyLog [A']) (τTyLog [A']) ttt fft
-- -- --   TermLog≤₁ {k = k} N f< [A] (ϝᵣ mε tA' fA') t N<
-- -- --     | Shp
-- -- --     with ≤-trans (≤₊-s-swap _ _) N<
-- -- --   TermLog≤₁ {k = k} (1+ N) f< [A] (ϝᵣ mε tA' fA') t N<
-- -- --     | Shp | ≤-s K< =
-- -- --     TermLog≤₁ N (≤ₗ-add-r f<) [A] tA' t (≤-trans (≤₊-l _ (μTy fA')) (≤-trans (≤₊-assoc-r {l = μTy [A]}) K<)) ,
-- -- --     TermLog≤₁ N (≤ₗ-add-r f<) [A] fA' t (≤-trans (≤₊-trans-r (μTy [A]) (≤₊-r _ _)) K<)
  


-- -- --   -- ϝTermLogHelper :
-- -- --   --   ∀ {F G t k k′ k″ m} {mε : NotInLConNat m l}
-- -- --   --   ([tF] : ∀ {m' : Nat} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
-- -- --   --           ρ Wk.∷ Δ ⊆ Γ →
-- -- --   --           ⊢ Δ / lε' → Δ / lε' ⊩⟨ k′ ⟩ (wk ρ F))
-- -- --   --   ([tG] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --         {a : Term m'} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
-- -- --   --         (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --         ([tF] {≤ε = ≤ε} [ρ] ⊢Δ) →
-- -- --   --         (k′ LogRel./ logRelRec k′ ⊩¹ Δ) lε'
-- -- --   --         (subst (consSubst var a) (wk (lift ρ) G)))
-- -- --   --   ([tt] : ∀ {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --         {a : Term m'} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Btrue l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'}
-- -- --   --         ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
-- -- --   --         ([a] : (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --              ([tF] {≤ε = ≤ε} [ρ] ⊢Δ)) →
-- -- --   --         (k′ LogRel./ logRelRec k′ ⊩¹ Δ ∷ lε' /
-- -- --   --           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --   --         (subst (consSubst var a) (wk (lift ρ) G)) ([tG] [ρ] ⊢Δ [a]))
-- -- --   --   ([fF] : ∀ {m' : Nat} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
-- -- --   --           ρ Wk.∷ Δ ⊆ Γ →
-- -- --   --           ⊢ Δ / lε' → Δ / lε' ⊩⟨ k″ ⟩ (wk ρ F))
-- -- --   --   ([fG] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --         {a : Term m'} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
-- -- --   --         (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --         ([fF] {≤ε = ≤ε} [ρ] ⊢Δ) →
-- -- --   --         (k″ LogRel./ logRelRec k″ ⊩¹ Δ) lε'
-- -- --   --         (subst (consSubst var a) (wk (lift ρ) G)))
-- -- --   --   ([ft] : ∀ {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --         {a : Term m'} {l' : LCon}
-- -- --   --         {≤ε : (addₗ m Bfalse l) ≤ₗ l'}
-- -- --   --         {lε' : ⊢ₗ l'}
-- -- --   --         ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
-- -- --   --         ([a] : (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --              ([fF] {≤ε = ≤ε} [ρ] ⊢Δ)) →
-- -- --   --         (k″ LogRel./ logRelRec k″ ⊩¹ Δ ∷ lε' /
-- -- --   --           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --   --         (subst (consSubst var a) (wk (lift ρ) G)) ([fG] {≤ε = ≤ε} [ρ] ⊢Δ [a]))
-- -- --   --   ([F] : ∀ {m' : Nat} {l' : LCon}
-- -- --   --          {≤ε : l ≤ₗ l'}
-- -- --   --          {lε' : ⊢ₗ l'} {ρ : Wk m' n} {Δ : Con Term m'} →
-- -- --   --            ρ Wk.∷ Δ ⊆ Γ →
-- -- --   --            ⊢ Δ / lε' → Δ / lε' ⊩⟨ k ⟩ (wk ρ F))
-- -- --   --   ([G] :{m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --             {a : Term m'} {l' : LCon}
-- -- --   --             {≤ε : l ≤ₗ l'}
-- -- --   --             {lε' : ⊢ₗ l'} ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε') →
-- -- --   --             (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --             ([F] {≤ε = ≤ε} [ρ] ⊢Δ) →
-- -- --   --             (k LogRel./ logRelRec k ⊩¹ Δ) lε'
-- -- --   --             (subst (consSubst var a) (wk (lift ρ) G)))     
-- -- --   --        {m' : Nat} {ρ : Wk m' n} {Δ : Con Term m'}
-- -- --   --          {a : Term m'} {l' : LCon}
-- -- --   --          {≤ε : l ≤ₗ l'}
-- -- --   --          {lε' : ⊢ₗ l'}
-- -- --   --          ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ / lε')
-- -- --   --          ([a] : (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' / a) (wk ρ F)
-- -- --   --            ([F] {≤ε = ≤ε} [ρ] ⊢Δ)) →
-- -- --   --          (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' /
-- -- --   --            gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --   --          (subst (consSubst var a) (wk (lift ρ) G)) ([G] {≤ε = ≤ε} [ρ] ⊢Δ [a])
-- -- --   -- ϝTermLogHelper {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
-- -- --   --   with decidInLConNat l' m
-- -- --   -- ϝTermLogHelper {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
-- -- --   --   | TS.inj₁ (TS.inj₁ inl) =
-- -- --   --   let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --   --       [T] = [tt] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --   --   in TermLog≤₁ _ (≤ₗ-id _) ([tG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _)
-- -- --   -- ϝTermLogHelper {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
-- -- --   --   | TS.inj₁ (TS.inj₂ inl) =
-- -- --   --   let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --   --       [T] = [ft] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --   --   in TermLog≤₁ _ (≤ₗ-id _) ([fG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _)
-- -- --   -- ϝTermLogHelper {m = m} [tF] [tG] [tt] [fF] [fG] [ft] [F] [G] {l' = l'} {≤ε = ≤ε} [ρ] ⊢Δ [a]
-- -- --   --   | TS.inj₂ notinl =
-- -- --   --   let ⊢Δ' = λ {b} → (τCon _ _ b notinl ⊢Δ)
-- -- --   --       [ta'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --   --       [fa'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --   --       [tT] = [tt] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [ta']
-- -- --   --       [fT] = [ft] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [fa']
-- -- --   --   in
-- -- --   --     ϝTermLog ([G] [ρ] ⊢Δ [a]) ([tG] [ρ] ⊢Δ' [ta']) ([fG] [ρ] ⊢Δ' [fa']) [tT] [fT]

-- -- --   -- ϝTermLogW : ∀ {A t k k′ k″ m mε} N [A]
-- -- --   --          (p : Γ / ⊢ₗ• l lε m Btrue mε   ⊩⟨ k′ ⟩ A) 
-- -- --   --          (q : Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ A)
-- -- --   --          → Γ / ⊢ₗ• l lε m Btrue mε ⊩⟨ k′ ⟩ t ∷ A / p
-- -- --   --          → Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ t ∷ A / q
-- -- --   --          → (((μTy p) + (μTy q)) ≤ N)
-- -- --   --          → Γ / lε ⊩⟨ k ⟩ t ∷ A / (Bᵣ BΠ [A])
-- -- --   -- ϝTermLogW {k = k} N (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft N<
-- -- --   --   with goodCasesRefl {k = k} (Bᵣ′ BΠ F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
-- -- --   --        (λ {_} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext) p
-- -- --   --   with goodCasesRefl {k = k} (Bᵣ′ BΠ F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A) [F]
-- -- --   --        (λ {_} {ρ} {Δ} {a} {l'} {≤ε} → [G] {_} {_} {_} {_} {_} {λ n b inl → ≤ε n b (InThere _ inl _ _)}) G-ext) q
-- -- --   -- ϝTermLogW N BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --          (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
-- -- --   --          (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
-- -- --   --          (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft]) N<
-- -- --   --          | Bᵥ BΠ BA′ tBB tBA≡B
-- -- --   --          | Bᵥ BΠ BA″ fBB fBA≡B
-- -- --   --          with whrDet* (τRed* (red D) , Πₙ) (red tD , Πₙ)
-- -- --   --          with whrDet* (τRed* (red D) , Πₙ) (red fD , Πₙ)
-- -- --   -- ϝTermLogW {t = t} {k = k} {m = m} {mε = mε} N BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --   --          (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
-- -- --   --          (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
-- -- --   --          (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft]) N<
-- -- --   --          | Bᵥ BΠ BA′ tBB tBA≡B
-- -- --   --          | Bᵥ BΠ BA″ fBB fBA≡B
-- -- --   --          | PE.refl | PE.refl =
-- -- --   --          ϝⱼ t⊢t f⊢t , (≅ₜ-ϝ tt≡t ft≡t , ((λ {_} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} [a] [b] a≡b → {!!}) ,
-- -- --   --            λ {_} {ρ} {Δ} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] →
-- -- --   --              let Helper : ((InLConNat m Btrue l') TS.⊎ (InLConNat m Bfalse l')) TS.⊎ (NotInLConNat m l') →
-- -- --   --                           (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' /
-- -- --   --                           gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --   --                         (subst (consSubst var a) (wk (lift ρ) G)) ([G] {≤ε = ≤ε} [ρ] ⊢Δ [a])
-- -- --   --                  Helper =
-- -- --   --                    (λ {(TS.inj₁ (TS.inj₁ inl)) → let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --   --                                                      [T] = [tt] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --   --                                                   in TermLog≤₁ _ (≤ₗ-id _) ([tG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --   --                       (TS.inj₁ (TS.inj₂ inl)) → let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --   --                                                     [T] = [ft] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --   --                                                 in TermLog≤₁ _ (≤ₗ-id _) ([fG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --   --                       (TS.inj₂ notinl) → let ⊢Δ' = λ {b} → (τCon _ _ b notinl ⊢Δ)
-- -- --   --                                              [ta'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --   --                                              [fa'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --   --                                              [tT] = [tt] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [ta']
-- -- --   --                                              [fT] = [ft] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [fa']
-- -- --   --                                          in ϝTermLog ([G] [ρ] ⊢Δ [a]) ([tG] [ρ] ⊢Δ' [ta']) ([fG] [ρ] ⊢Δ' [fa']) [tT] [fT]})
-- -- --   --              in Helper (decidInLConNat l' m)))
-- -- --   --            -- ϝTermLog _ _ _ ([tt] {_} {_} {_} {_} {_} {λ n b nε → ≤ε n b {!!}} [ρ] (Con≤ (λ n b nε → nε) ⊢Δ) {!!}) {!!}))
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p (emb 0<1 q) tt ft (≤-s N<)
-- -- --   --   | Bᵥ BΠ BA′ tBB tBA≡B
-- -- --   --   | emb¹⁰ fA = ϝTermLogW N BA p q tt ft N<
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft (≤-s N<)
-- -- --   --   | Bᵥ BΠ BA′ tBB tBA≡B
-- -- --   --   | ϝᵣ-r (Bᵣ BΠ BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = {!!}
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb 0<1 p) q tt ft (≤-s N<)
-- -- --   --   | emb¹⁰ [A] | _  = ϝTermLogW N BA p q tt ft N<
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q ( ttt , tft ) ft (≤-s N<)
-- -- --   --   | ϝᵣ-r (Bᵣ BΠ BA′) tBAt tBAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
-- -- --   --   | Bᵥ BΠ BA″ fBB fBA≡B =
-- -- --   --     let [tt] = ϝTermLogW N BA′ ttp tfp ttt tft (≤-trans (≤₊-l _ _) N<)
-- -- --   --     in ϝTermLogW N BA (Bᵣ BΠ BA′) q [tt] ft (≤-0 N)
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p (emb 0<1 q) tt ft (≤-s N<)
-- -- --   --   | ϝᵣ-r (Bᵣ BΠ BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB
-- -- --   --   | emb¹⁰ [A] = ϝTermLogW N BA p q tt ft (≤-trans (≤₊-s-swap _ _) N<)
-- -- --   -- ϝTermLogW (1+ N) BA@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft (≤-s N<)
-- -- --   --   | ϝᵣ-r (Bᵣ BΠ BA′) tBAt tBAf ttp tfp tA≡B ttA≡B tfA≡B ttAB tfAB
-- -- --   --   | ϝᵣ-r (Bᵣ BΠ BA″) fBAt fBAf ftp ffp fA≡B ftA≡B ffA≡B ftAB ffAB = {!!}

-- -- --   ϝTermLog : ∀ {A t k k′ k″ m mε} [A]
-- -- --            (p : Γ / ⊢ₗ• l lε m Btrue mε   ⊩⟨ k′ ⟩ A) 
-- -- --            (q : Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ A)
-- -- --            → Γ / ⊢ₗ• l lε m Btrue mε ⊩⟨ k′ ⟩ t ∷ A / p
-- -- --            → Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ t ∷ A / q
-- -- --            → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
-- -- --   ϝTermLog {k = k} (Uᵣ UA) p q tt ft = ϝU {k = k} (μTy p + μTy q) UA p q tt ft (≤-refl _)
-- -- --   ϝTermLog {k = k} (𝔹ᵣ 𝔹A) p q tt ft = ϝ𝔹 {k = k} 𝔹A p q tt ft
-- -- --   ϝTermLog {k = k} (ℕᵣ ℕA) p q tt ft = ϝℕ {k = k} ℕA p q tt ft
-- -- --   ϝTermLog {k = k} (ne neA) p q tt ft = ϝNe {k = k} neA p q tt ft
-- -- --   ϝTermLog (emb 0<1 [A]) p q tt ft = {!!} -- ϝTermLog [A] p q tt ft
-- -- --   ϝTermLog {t = t} {k = k} {m = m} {mε = mε} BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --            (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
-- -- --            (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
-- -- --            (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft])
-- -- --            with whrDet* (τRed* (red D) , Πₙ) (red tD , Πₙ)
-- -- --            with whrDet* (τRed* (red D) , Πₙ) (red fD , Πₙ)
-- -- --   ϝTermLog {t = t} {k = k} {m = m} {mε = mε} BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --            (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
-- -- --            (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
-- -- --            (t⊢t , tt≡t , [tt≡t] , [tt]) (f⊢t , ft≡t , [ft≡t] , [ft])
-- -- --            | PE.refl | PE.refl =
-- -- --            ϝⱼ t⊢t f⊢t , (≅ₜ-ϝ tt≡t ft≡t , ((λ {_} {ρ} {Δ} {a} {b} {l'} {≤ε} {lε'} [a] [b] a≡b → {!!}) ,
-- -- --              λ {_} {ρ} {Δ} {a} {l'} {≤ε} {lε'} [ρ] ⊢Δ [a] →
-- -- --                let Helper : ((InLConNat m Btrue l') TS.⊎ (InLConNat m Bfalse l')) TS.⊎ (NotInLConNat m l') →
-- -- --                             (k LogRel./ logRelRec k ⊩¹ Δ ∷ lε' /
-- -- --                             gen Appkind (wk ρ t GenTs.∷ (a GenTs.∷ [])))
-- -- --                           (subst (consSubst var a) (wk (lift ρ) G)) ([G] {≤ε = ≤ε} [ρ] ⊢Δ [a])
-- -- --                    Helper =
-- -- --                      (λ {(TS.inj₁ (TS.inj₁ inl)) → {!!} ; --let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --                                                       -- [T] = [tt] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --                                                     -- in TermLog≤₁ _ (≤ₗ-id _) ([tG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --                         (TS.inj₁ (TS.inj₂ inl)) → {!!} ; --let [a'] = TermLog≤₁ _ (≤ₗ-id _) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ) [a] (≤-refl _)
-- -- --                                                       -- [T] = [ft] {≤ε = ≤ₗ-add _ _ _ ≤ε inl} [ρ] ⊢Δ [a']
-- -- --                                                   -- in TermLog≤₁ _ (≤ₗ-id _) ([fG] [ρ] ⊢Δ [a']) ([G] [ρ] ⊢Δ [a]) [T] (≤-refl _) ;
-- -- --                         (TS.inj₂ notinl) → let ⊢Δ' = λ {b} → (τCon _ _ b notinl ⊢Δ)
-- -- --                                                [ta'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([tF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --                                                [fa'] = TermLog≤₁ _ (≤ₗ-add-r (≤ₗ-id _)) ([F] [ρ] ⊢Δ) ([fF] [ρ] ⊢Δ') [a] (≤-refl _)
-- -- --                                                [tT] = [tt] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [ta']
-- -- --                                                [fT] = [ft] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r ≤ε) (InHereNat _)} [ρ] (⊢Δ') [fa']
-- -- --                                            in ϝTermLog ([G] [ρ] ⊢Δ [a]) ([tG] [ρ] ⊢Δ' [ta']) ([fG] [ρ] ⊢Δ' [fa']) [tT] [fT]})
-- -- --                in Helper (decidInLConNat l' m)))
-- -- --   ϝTermLog {k = k} (Bᵣ BΠ BA) p q tt ft
-- -- --     = {!!} -- ϝTermLogW {k = k} BA p q tt ft N<
-- -- --   ϝTermLog {k = k} (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) p q tt ft
-- -- --     = {!!}
-- -- --   ϝTermLog (ϝᵣ mε tA fA) p q tt ft = {!!} , {!!}
    
