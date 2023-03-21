{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Weakening where

open import Definition.Untyped as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties
open import Definition.Typed

open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    ℓ n m  : Nat
    A B t u    : Term n
    Γ  : Con Term n
    Δ  : Con Term m
    Δ′ : Con Term ℓ
    ρ  : Wk m n
    ρ′ : Wk n ℓ
-- Weakening type

data _∷_⊆_ : Wk m n → Con Term m → Con Term n → Set where
  id   :             id     ∷ Γ            ⊆ Γ
  step : ρ ∷ Δ ⊆ Γ → step ρ ∷ Δ ∙ A        ⊆ Γ
  lift : ρ ∷ Δ ⊆ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ⊆ Γ ∙ A


-- -- Weakening composition

_•ₜ_ : ρ ∷ Γ ⊆ Δ → ρ′ ∷ Δ ⊆ Δ′ → ρ • ρ′ ∷ Γ ⊆ Δ′
id     •ₜ η′ = η′
step η •ₜ η′ = step (η •ₜ η′)
lift η •ₜ id = lift η
lift η •ₜ step η′ = step (η •ₜ η′)
_•ₜ_ {ρ = lift ρ} {ρ′ = lift ρ′} {Δ′ = Δ′ ∙ A} (lift η) (lift η′) =
  PE.subst (λ x → lift (ρ • ρ′) ∷ x ⊆ Δ′ ∙ A)
           (PE.cong₂ _∙_ PE.refl (PE.sym (wk-comp ρ ρ′ A)))
           (lift (η •ₜ η′))


-- Weakening of judgements

wkIndex : ∀ {l} {lε : ⊢ₗ l} {n} → ρ ∷ Δ ⊆ Γ →
        let ρA = U.wk ρ A
            ρn = wkVar ρ n
        in  ⊢ Δ / lε → n ∷ A ∈ Γ → ρn ∷ ρA ∈ Δ
wkIndex id ⊢Δ i = PE.subst (λ x → _ ∷ x ∈ _) (PE.sym (wk-id _)) i
wkIndex (step ρ) (⊢Δ ∙ A) i = PE.subst (λ x → _ ∷ x ∈ _)
                                       (wk1-wk _ _)
                                       (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) (⊢Δ ∙ A) (there i) = PE.subst (λ x → _ ∷ x ∈ _)
                                               (wk1-wk≡lift-wk1 _ _)
                                               (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) ⊢Δ here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ∈ G)
               (wk1-wk≡lift-wk1 _ _)
               here
wkIndex (step ρ) (ϝ g d) i = wkIndex (step ρ) g i
wkIndex (lift ρ) (ϝ g d) (there i) = wkIndex (lift ρ) g (there i)

mutual
  wk : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
     let ρA = U.wk ρ A
     in  ⊢ Δ / lε → Γ / lε ⊢ A → Δ / lε ⊢ ρA
  wk ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
--  wk ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
--  wk ρ ⊢Δ (Unitⱼ ⊢Γ) = Unitⱼ ⊢Δ
  wk ρ ⊢Δ (Uⱼ ⊢Γ) = Uⱼ ⊢Δ
  wk ρ ⊢Δ (Πⱼ F ▹ G) = let ρF = wk ρ ⊢Δ F
                       in  Πⱼ ρF ▹ (wk (lift ρ) (⊢Δ ∙ ρF) G)
  wk ρ ⊢Δ (Σⱼ F ▹ G) = let ρF = wk ρ ⊢Δ F
                       in  Σⱼ ρF ▹ (wk (lift ρ) (⊢Δ ∙ ρF) G)
  wk ρ ⊢Δ (univ A) = univ (wkTerm ρ ⊢Δ A)
  wk ρ ⊢Δ (𝔹ⱼ ⊢Γ) = 𝔹ⱼ ⊢Δ
  wk ρ ⊢Δ (ϝⱼ g d) = ϝⱼ (wk ρ (τCon _ _ _ _ ⊢Δ) g) (wk ρ (τCon _ _ _ _ ⊢Δ) d)
  
  wkTerm : ∀ {l} {lε : ⊢ₗ l} {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρt = U.wk ρ t
         in ⊢ Δ / lε → Γ / lε ⊢ t ∷ A → Δ / lε ⊢ ρt ∷ ρA
  wkTerm ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wkTerm ρ ⊢Δ (𝔹ⱼ ⊢Γ) = 𝔹ⱼ ⊢Δ
--  wkTerm ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
--  wkTerm ρ ⊢Δ (Unitⱼ ⊢Γ) = Unitⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Πⱼ F ▹ G) = let ρF = wkTerm ρ ⊢Δ F
                           in  Πⱼ ρF ▹ (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G)
  wkTerm ρ ⊢Δ (Σⱼ F ▹ G) = let ρF = wkTerm ρ ⊢Δ F
                           in  Σⱼ ρF ▹ (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G)
  wkTerm ρ ⊢Δ (var ⊢Γ x) = var ⊢Δ (wkIndex ρ ⊢Δ x)
  wkTerm ρ ⊢Δ (lamⱼ F t) = let ρF = wk ρ ⊢Δ F
                           in lamⱼ ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) t)
  wkTerm ρ ⊢Δ (_∘ⱼ_ {G = G} g a) = PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                           (PE.sym (wk-β G))
                                           (wkTerm ρ ⊢Δ g ∘ⱼ wkTerm ρ ⊢Δ a)
  wkTerm ρ ⊢Δ (prodⱼ {G = G} ⊢F ⊢G t u) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
        ρu = wkTerm ρ ⊢Δ u
        ρu = PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) ρu
    in  prodⱼ ρF ρG ρt ρu
  wkTerm ρ ⊢Δ (fstⱼ {G = G} ⊢F ⊢G t) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
    in  fstⱼ ρF ρG ρt
  wkTerm ρ ⊢Δ (sndⱼ {G = G} ⊢F ⊢G t) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
    in  PE.subst (λ x → _ / _ ⊢ snd _ ∷ x) (PE.sym (wk-β G)) (sndⱼ ρF ρG ρt)
  wkTerm ρ ⊢Δ (zeroⱼ ⊢Γ) = zeroⱼ ⊢Δ
  wkTerm ρ ⊢Δ (sucⱼ n) = sucⱼ (wkTerm ρ ⊢Δ n)
  wkTerm ρ ⊢Δ (trueⱼ ⊢Γ) = trueⱼ ⊢Δ
  wkTerm ρ ⊢Δ (falseⱼ ⊢Γ) = falseⱼ ⊢Δ
  wkTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrecⱼ {G = G} {s = s} ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ / _ ⊢ natrec _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (natrecⱼ (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢G)
                      (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢z))
                      (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                (wk-β-natrec ρ G)
                                (wkTerm [ρ] ⊢Δ ⊢s))
                      (wkTerm [ρ] ⊢Δ ⊢n))
--  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrecⱼ {A = A} {e = e} ⊢A ⊢e) =
--    (Emptyrecⱼ (wk [ρ] ⊢Δ ⊢A) (wkTerm [ρ] ⊢Δ ⊢e))
--  wkTerm ρ ⊢Δ (starⱼ ⊢Γ) = starⱼ ⊢Δ
  wkTerm ρ ⊢Δ (conv t A≡B) = conv (wkTerm ρ ⊢Δ t) (wkEq ρ ⊢Δ A≡B)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrecⱼ {G = G} ⊢G ⊢t ⊢f ⊢n) =
    PE.subst (λ x → _ / _ ⊢ boolrec _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (boolrecⱼ (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢G)
                      (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢t))
                      (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢f))
                      (wkTerm [ρ] ⊢Δ ⊢n))
  wkTerm ρ ⊢Δ (αⱼ a) = αⱼ (wkTerm ρ ⊢Δ a)
  wkTerm ρ ⊢Δ (ϝⱼ g d) = ϝⱼ (wkTerm ρ (τCon _ _ _ _ ⊢Δ) g) (wkTerm ρ (τCon _ _ _ _ ⊢Δ) d)
  
  wkEq : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
       let ρA = U.wk ρ A
           ρB = U.wk ρ B
       in ⊢ Δ / lε → Γ / lε ⊢ A ≡ B → Δ / lε ⊢ ρA ≡ ρB
  wkEq ρ ⊢Δ (univ A≡B) = univ (wkEqTerm ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (refl A) = refl (wk ρ ⊢Δ A)
  wkEq ρ ⊢Δ (sym A≡B) = sym (wkEq ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (trans A≡B B≡C) = trans (wkEq ρ ⊢Δ A≡B) (wkEq ρ ⊢Δ B≡C)
  wkEq ρ ⊢Δ (Π-cong F F≡H G≡E) = let ρF = wk ρ ⊢Δ F
                                 in  Π-cong ρF (wkEq ρ ⊢Δ F≡H)
                                               (wkEq (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEq ρ ⊢Δ (Σ-cong F F≡H G≡E) = let ρF = wk ρ ⊢Δ F
                                 in  Σ-cong ρF (wkEq ρ ⊢Δ F≡H)
                                               (wkEq (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEq ρ ⊢Δ (ϝ-cong g d) = ϝ-cong (wkEq ρ (τCon _ _ _ _ ⊢Δ) g) (wkEq ρ (τCon _ _ _ _ ⊢Δ) d)
  
  wkEqTerm : {l : LCon} {lε : ⊢ₗ l} {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ / lε → Γ / lε ⊢ t ≡ u ∷ A → Δ / lε ⊢ ρt ≡ ρu ∷ ρA
  wkEqTerm ρ ⊢Δ (refl t) = refl (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (sym t≡u) = sym (wkEqTerm ρ ⊢Δ t≡u)
  wkEqTerm ρ ⊢Δ (trans t≡u u≡r) = trans (wkEqTerm ρ ⊢Δ t≡u) (wkEqTerm ρ ⊢Δ u≡r)
  wkEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (wkEqTerm ρ ⊢Δ t≡u) (wkEq ρ ⊢Δ A≡B)
  wkEqTerm ρ ⊢Δ (Π-cong F F≡H G≡E) =
    let ρF = wk ρ ⊢Δ F
    in  Π-cong ρF (wkEqTerm ρ ⊢Δ F≡H)
                  (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEqTerm ρ ⊢Δ (Σ-cong F F≡H G≡E) =
    let ρF = wk ρ ⊢Δ F
    in  Σ-cong ρF (wkEqTerm ρ ⊢Δ F≡H)
                  (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ / _ ⊢ _ ≡ _ ∷ x)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm ρ ⊢Δ f≡g) (wkEqTerm ρ ⊢Δ a≡b))
  wkEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {G = G} F ⊢t ⊢a) =
    let ρF = wk ρ ⊢Δ F
    in  PE.subst (λ x → _ / _ ⊢ _ ≡ _ ∷ x)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x → _ / _ ⊢ U.wk _ ((lam t) ∘ a) ≡ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (wkTerm ρ ⊢Δ ⊢a)))
  wkEqTerm ρ ⊢Δ (η-eq F f g f0≡g0) =
    let ρF = wk ρ ⊢Δ F
    in  η-eq ρF (wkTerm ρ ⊢Δ f)
                (wkTerm ρ ⊢Δ g)
                (PE.subst (λ t → _ / _ ⊢ t ∘ _ ≡ _ ∷ _)
                          (PE.sym (wk1-wk≡lift-wk1 _ _))
                          (PE.subst (λ t → _ / _ ⊢ _ ≡ t ∘ _ ∷ _)
                                    (PE.sym (wk1-wk≡lift-wk1 _ _))
                                    (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) f0≡g0)))
  wkEqTerm ρ ⊢Δ (fst-cong ⊢F ⊢G t≡t') =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
    in  fst-cong ρF ρG (wkEqTerm ρ ⊢Δ t≡t')
  wkEqTerm ρ ⊢Δ (snd-cong {G = G} ⊢F ⊢G t≡t') =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt≡t' = wkEqTerm ρ ⊢Δ t≡t'
    in  PE.subst (λ x → _ / _ ⊢ snd _ ≡ snd _ ∷ x) (PE.sym (wk-β G))
      (snd-cong ρF ρG ρt≡t')
  wkEqTerm ρ ⊢Δ (Σ-η {G = G} ⊢F ⊢G ⊢p ⊢r fst≡ snd≡) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρp = wkTerm ρ ⊢Δ ⊢p
        ρr = wkTerm ρ ⊢Δ ⊢r
        ρfst≡ = wkEqTerm ρ ⊢Δ fst≡
        ρsnd≡ = wkEqTerm ρ ⊢Δ snd≡
        ρsnd≡ = PE.subst (λ x → _ / _ ⊢ _ ≡ _ ∷ x)
                         (wk-β G)
                         ρsnd≡
    in  Σ-η ρF ρG ρp ρr ρfst≡ ρsnd≡
  wkEqTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₁ {G = G} ⊢F ⊢G t u) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρF ρG ρt ρu
  wkEqTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₂ {G = G} ⊢F ⊢G t u) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ / _ ⊢ _ ≡ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρF ρG ρt ρu)
  wkEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (wkEqTerm ρ ⊢Δ m≡n)
  wkEqTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-cong {s = s} {s′ = s′} {F = F}
                                     F≡F′ z≡z′ s≡s′ n≡n′) =
    PE.subst (λ x → Δ / _ ⊢ natrec _ _ _ _ ≡ _ ∷ x) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) F≡F′)
                          (PE.subst (λ x → Δ / _ ⊢ _ ≡ _ ∷ x) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ z≡z′))
                          (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s
                                             ≡ U.wk ρ s′ ∷ x)
                                    (wk-β-natrec _ F)
                                    (wkEqTerm [ρ] ⊢Δ s≡s′))
                          (wkEqTerm [ρ] ⊢Δ n≡n′))
  wkEqTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {_} {_} {z} {s} {F} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ / _ ⊢ natrec (U.wk (lift _) F) _ _ _ ≡ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ / _ ⊢ U.wk ρ z ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                    (wk-β-natrec _ F)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkEqTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {_} {_} {n} {z} {s} {F} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ / _ ⊢ natrec (U.wk (lift _) F) _ _ _
                      ≡ _ ∘ (natrec _ _ _ _) ∷ x)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                         (PE.subst (λ x → Δ / _ ⊢ U.wk ρ z ∷ x)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                   (wk-β-natrec _ F)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
--  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-cong {A = A} {A' = A'} {e = e} {e' = e'}
--                                  A≡A' e≡e') =
--    (Emptyrec-cong (wkEq [ρ] ⊢Δ A≡A')
--      (wkEqTerm [ρ] ⊢Δ e≡e'))
--  wkEqTerm ρ ⊢Δ (η-unit e e') = η-unit (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ e')
  wkEqTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-cong {F = F}
                                     F≡F′ t≡t′ f≡f′ n≡n′) =
    PE.subst (λ x → Δ / lε ⊢ boolrec _ _ _ _ ≡ _ ∷ x) (PE.sym (wk-β F))
             (boolrec-cong (wkEq (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) F≡F′)
                          (PE.subst (λ x → Δ / lε ⊢ _ ≡ _ ∷ x) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ t≡t′))
                          (PE.subst (λ x → Δ / lε ⊢ _ ≡ _ ∷ x) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ f≡f′))
                          (wkEqTerm [ρ] ⊢Δ n≡n′))
  wkEqTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-true {_} {_} {t} {f} {F} ⊢F ⊢t ⊢f) =
    PE.subst (λ x → Δ / _ ⊢ boolrec (U.wk (lift _) F) _ _ _ ≡ _ ∷ x)
             (PE.sym (wk-β F))
             (boolrec-true (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ / _ ⊢ U.wk ρ t ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢t))
                          (PE.subst (λ x → Δ / _ ⊢ U.wk ρ f ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢f)))
  wkEqTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-false {_} {_} {t} {f} {F} ⊢F ⊢t ⊢f) =
    PE.subst (λ x → Δ / _ ⊢ boolrec (U.wk (lift _) F) _ _ _ ≡ _ ∷ x)
             (PE.sym (wk-β F))
             (boolrec-false (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ / _ ⊢ U.wk ρ t ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢t))
                          (PE.subst (λ x → Δ / _ ⊢ U.wk ρ f ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢f)))
  wkEqTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (α-cong x₂) = α-cong (wkEqTerm [ρ] ⊢Δ x₂)
  wkEqTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (ϝ-cong g d) = ϝ-cong (wkEqTerm [ρ] (τCon _ _ _ _ ⊢Δ) g) (wkEqTerm [ρ] (τCon _ _ _ _ ⊢Δ) d)
  wkEqTerm {ρ = ρ} [ρ] ⊢Δ (α-conv ⊢t tε PE.refl PE.refl) = α-conv (wkTerm [ρ] ⊢Δ ⊢t) tε (wkNatToTerm ρ _) (wkBboolToTerm ρ _)
  

mutual
  wkRed : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ / lε → Γ / lε ⊢ A ⇒ B → Δ / lε ⊢ ρA ⇒ ρB
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : {l : LCon} {lε : ⊢ₗ l} {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ / lε → Γ / lε ⊢ t ⇒ u ∷ A → Δ / lε ⊢ ρt ⇒ ρu ∷ ρA
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {B = B} t⇒u a) =
    PE.subst (λ x → _ / _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a))
  wkRedTerm ρ ⊢Δ (β-red {_} {_} {A} {B} {a} {t} ⊢A ⊢t ⊢a) =
    let ⊢ρA = wk ρ ⊢Δ ⊢A
    in  PE.subst (λ x → _ / _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ / _ ⊢ U.wk _ ((lam t) ∘ a) ⇒ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ⊢ρA (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (wkTerm ρ ⊢Δ ⊢a)))
  wkRedTerm ρ ⊢Δ (fst-subst ⊢F ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  fst-subst ρF ρG ρt⇒
  wkRedTerm ρ ⊢Δ (snd-subst {G = G} ⊢F ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  PE.subst (λ x → _ / _ ⊢ snd _ ⇒ snd _ ∷ x) (PE.sym (wk-β G))
      (snd-subst ρF ρG ρt⇒)
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₁ {G = G} ⊢F ⊢G t u) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρF ρG ρt ρu
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₂ {G = G} ⊢F ⊢G t u) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ / _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρF ρG ρt ρu)
  wkRedTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-subst {s = s} {F = F} ⊢F ⊢z ⊢s n⇒n′) =
    PE.subst (λ x → _ / _ ⊢ natrec _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β F))
             (natrec-subst (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                           (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                     (wk-β-natrec _ F)
                                     (wkTerm [ρ] ⊢Δ ⊢s))
                           (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {s = s} {F = F} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ / _ ⊢ natrec (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                    (wk-β-natrec ρ F)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkRedTerm {l = l} {lε = lε} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {s = s} {F = F} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ / _ ⊢ natrec _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                         (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ / lε ⊢ U.wk ρ s ∷ x)
                                   (wk-β-natrec ρ F)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
--  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-subst {A = A} ⊢A n⇒n′) =
--    (Emptyrec-subst (wk [ρ] ⊢Δ ⊢A)
--                    (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-subst {F = F} ⊢F ⊢t ⊢f n⇒n′) =
    PE.subst (λ x → _ / _ ⊢ boolrec _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β F))
             (boolrec-subst (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢F)
                           (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢t))
                           (PE.subst (λ x → _ / _ ⊢ _ ∷ x) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢f))
                           (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-true {F = F} ⊢F ⊢t ⊢f) =
    PE.subst (λ x → _ / _ ⊢ boolrec (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x)
             (PE.sym (wk-β F))
             (boolrec-true (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢t))
                          (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢f)))
  wkRedTerm {l = l} {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (boolrec-false {F = F} ⊢F ⊢t ⊢f) =
    PE.subst (λ x → _ / _ ⊢ boolrec (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x)
             (PE.sym (wk-β F))
             (boolrec-false (wk (lift [ρ]) (⊢Δ ∙ 𝔹ⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢t))
                          (PE.subst (λ x → _ / _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢f)))
  wkRedTerm [ρ] ⊢Δ (α-subst n⇒n') = α-subst (wkRedTerm [ρ] ⊢Δ n⇒n')
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (α-red ⊢n inl PE.refl PE.refl) = α-red (wkTerm [ρ] ⊢Δ ⊢n) inl (wkNatToTerm ρ _) (wkBboolToTerm ρ _)
  
wkRed* : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ / lε → Γ / lε ⊢ A ⇒* B → Δ / lε ⊢ ρA ⇒* ρB
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ ⊢Δ A⇒A′ ⇨ wkRed* ρ ⊢Δ A′⇒*B

wkRed*Term : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ / lε → (_/_⊢_⇒*_∷_ Γ lε t u A) → (_/_⊢_⇒*_∷_ Δ lε ρt ρu ρA)
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ ⊢Δ t⇒t′ ⇨ wkRed*Term ρ ⊢Δ t′⇒*u

wkRed:*: : ∀ {l} {lε : ⊢ₗ l} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρB = U.wk ρ B
         in ⊢ Δ / lε → Γ / lε ⊢ A :⇒*: B → Δ / lε ⊢ ρA :⇒*: ρB
wkRed:*: ρ ⊢Δ [ ⊢A , ⊢B , D ] = [ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]

wkRed:*:Term : ∀ {l} {lε : ⊢ₗ l} →  ρ ∷ Δ ⊆ Γ →
             let ρA = U.wk ρ A
                 ρt = U.wk ρ t
                 ρu = U.wk ρ u
             in ⊢ Δ / lε → (_/_⊢_:⇒*:_∷_ Γ lε t u A) → (_/_⊢_:⇒*:_∷_ Δ lε ρt ρu ρA)
wkRed:*:Term ρ ⊢Δ [ ⊢t , ⊢u , d ] =
  [ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]
