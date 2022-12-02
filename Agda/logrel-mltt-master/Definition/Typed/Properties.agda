{-# OPTIONS  --without-K --safe #-}

module Definition.Typed.Properties where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    b : Bbool
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l
    A A′ B B′ U′ : Term n
    a t u u′ : Term n

-- Escape context extraction

wfContext : ⊢ (Γ ∙ A) / lε → ⊢ Γ / lε
wfContext (⊢Γ ∙ F′) = ⊢Γ
wfContext (ϝ l r) = ϝ (wfContext l) (wfContext r)

wfTerm : Γ / lε ⊢ t ∷ A → ⊢ Γ / lε
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Unitⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ F t) with wfTerm t
wfTerm (lamⱼ F t) | (⊢Γ ∙ F′) = ⊢Γ
wfTerm (lamⱼ F t) | ϝ l r = ϝ (wfContext l) (wfContext r)
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (starⱼ ⊢Γ) = ⊢Γ
wfTerm (conv t A≡B) = wfTerm t
wfTerm (Σⱼ a ▹ a₁) = wfTerm a
wfTerm (prodⱼ F G a a₁) = wfTerm a
wfTerm (fstⱼ _ _ a) = wfTerm a
wfTerm (sndⱼ _ _ a) = wfTerm a
wfTerm (𝔹ⱼ x) = x
wfTerm (trueⱼ x) = x
wfTerm (falseⱼ x) = x
wfTerm (boolrecⱼ F z s b) = wfTerm b
wfTerm (αⱼ x) = wfTerm x
wfTerm (ϝⱼ l r) = ϝ (wfTerm l) (wfTerm r)

wf : Γ / lε ⊢ A → ⊢ Γ / lε
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Unitⱼ ⊢Γ) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (Πⱼ F ▹ G) = wf F
wf (Σⱼ F ▹ G) = wf F
wf (univ A) = wfTerm A
wf (𝔹ⱼ x) = x
wf (ϝⱼ l r) = ϝ (wf l) (wf r)

wfEqTerm : Γ / lε ⊢ t ≡ u ∷ A → ⊢ Γ / lε
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n
wfEqTerm (Emptyrec-cong A≡A' e≡e') = wfEqTerm e≡e'
wfEqTerm (η-unit e e') = wfTerm e
wfEqTerm (Σ-cong F _ _) = wf F
wfEqTerm (fst-cong _ _ a) = wfEqTerm a
wfEqTerm (snd-cong _ _ a) = wfEqTerm a
wfEqTerm (Σ-η _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₁ F G x x₁) = wfTerm x
wfEqTerm (Σ-β₂ F G x x₁) = wfTerm x
wfEqTerm (boolrec-cong F≡F′ t≡t′ f≡f′ b≡b′) = wfEqTerm t≡t′
wfEqTerm (boolrec-true F t f) = wfTerm t
wfEqTerm (boolrec-false F t f) = wfTerm f
wfEqTerm (α-cong x) = wfEqTerm x
wfEqTerm (ϝ-cong l r) = ϝ (wfEqTerm l) (wfEqTerm r)
wfEqTerm (α-conv x tε) = wfTerm x

wfEq : Γ / lε ⊢ A ≡ B → ⊢ Γ / lε
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wf F
wfEq (Σ-cong F x₁ x₂) = wf F
wfEq (ϝ-cong l r) = ϝ (wfEq l) (wfEq r)


-- Reduction is a subset of conversion

subsetTerm : Γ / lε ⊢ t ⇒ u ∷ A → Γ / lε ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (Emptyrec-subst A n⇒n′) =
  Emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t a) = β-red A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (fst-subst F G x) = fst-cong F G (subsetTerm x)
subsetTerm (snd-subst F G x) = snd-cong F G (subsetTerm x)
subsetTerm (Σ-β₁ F G x x₁) = Σ-β₁ F G x x₁
subsetTerm (Σ-β₂ F G x x₁) = Σ-β₂ F G x x₁
subsetTerm (boolrec-subst F t f b⇒b') = boolrec-cong (refl F) (refl t) (refl f) (subsetTerm b⇒b')
subsetTerm (boolrec-true F t f) = boolrec-true F t f
subsetTerm (boolrec-false F t f) = boolrec-false F t f
subsetTerm (α-subst t⇒u) = α-cong (subsetTerm t⇒u)
subsetTerm (α-red {b = b} ⊢n inl) = α-conv ⊢n inl -- α-conv x (InHere _ b _)
  
subset : Γ / lε ⊢ A ⇒ B → Γ / lε ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : Γ / lε ⊢ t ⇒* u ∷ A → Γ / lε ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : Γ / lε ⊢ A ⇒* B → Γ / lε ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)

-- Can extract left-part of a reduction

redFirstTerm : Γ / lε ⊢ t ⇒ u ∷ A → Γ / lε ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A t a) = (lamⱼ A t) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (Emptyrec-subst A n⇒n′) = Emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (fst-subst F G x) = fstⱼ F G (redFirstTerm x)
redFirstTerm (snd-subst F G x) = sndⱼ F G (redFirstTerm x)
redFirstTerm (Σ-β₁ F G x x₁) = fstⱼ F G (prodⱼ F G x x₁)
redFirstTerm (Σ-β₂ F G x x₁) = sndⱼ F G (prodⱼ F G x x₁)
redFirstTerm (boolrec-subst F t f b⇒b') = boolrecⱼ F t f (redFirstTerm b⇒b')
redFirstTerm (boolrec-true F t f) = boolrecⱼ F t f (trueⱼ (wfTerm t))
redFirstTerm (boolrec-false F t f) = boolrecⱼ F t f (falseⱼ (wfTerm f))
redFirstTerm (α-subst t⇒u) = αⱼ (redFirstTerm t⇒u)
redFirstTerm (α-red ⊢n inl) = αⱼ ⊢n -- αⱼ x


redFirst : Γ / lε ⊢ A ⇒ B → Γ / lε ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : Γ / lε ⊢ t ⇒* u ∷ A → Γ / lε ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : Γ / lε ⊢ A ⇒* B → Γ / lε ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′


-- No neutral terms are well-formed in an empty context
mutual 
  noNe : ∀ {l : LCon} {lε : ⊢ₗ l} → ε / lε ⊢ t ∷ A → Neutral t → ⊥
  noNe (conv ⊢t x) n = noNe ⊢t n
  noNe (var x₁ ()) (var x)
  noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
  noNe (fstⱼ _ _ ⊢t) (fstₙ neT) = noNe ⊢t neT
  noNe (sndⱼ _ _ ⊢t) (sndₙ neT) = noNe ⊢t neT
  noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
  noNe (Emptyrecⱼ A ⊢e) (Emptyrecₙ neT) = noNe ⊢e neT
  noNe (boolrecⱼ F ⊢t ⊢f ⊢x) (boolrecₙ neT) = noNe ⊢x neT
  noNe (αⱼ ⊢t) (αₙ cneT) = noContainsNe ⊢t cneT
  noNe (ϝⱼ ⊢l ⊢r) neT = noNe ⊢l neT

  noContainsNe : ∀ {l : LCon} {lε : ⊢ₗ l} → ε / lε ⊢ t ∷ A → ContainsNeutral t → ⊥
  noContainsNe ⊢t (ncontn neT) = noNe ⊢t neT
  noContainsNe (sucⱼ ⊢t) (Scontn cneT) = noContainsNe ⊢t cneT
  noContainsNe (conv  ⊢t x) (Scontn cneT) = noContainsNe ⊢t (Scontn cneT)
  noContainsNe (ϝⱼ ⊢l ⊢r) (Scontn cneT) = noContainsNe ⊢l (Scontn cneT)

--Neutrals do not weak head reduce

mutual
  αneRedTerm : ∀ {l : LCon} {lε : ⊢ₗ l} → (d : Γ / lε ⊢ t ⇒ u ∷ A) (n : αNeutral {l} {lε} t) → ⊥
  αneRedTerm (conv d x) n = αneRedTerm d n
  αneRedTerm (app-subst d x) (∘ₙ n) = αneRedTerm d n
  αneRedTerm (β-red x x₁ x₂) (∘ₙ ())
  αneRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = αneRedTerm d n₁
  αneRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
  αneRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
  αneRedTerm (Emptyrec-subst x d) (Emptyrecₙ n₁) = αneRedTerm d n₁
  αneRedTerm (fst-subst _ _ d) (fstₙ n) = αneRedTerm d n
  αneRedTerm (snd-subst _ _ d) (sndₙ n) = αneRedTerm d n
  αneRedTerm (Σ-β₁ F G x x₁) (fstₙ ())
  αneRedTerm (Σ-β₂ F G x x₁) (sndₙ ())
  αneRedTerm (boolrec-subst x x₁ x₂ d) (boolrecₙ b₁) = αneRedTerm d b₁
  αneRedTerm (boolrec-true x x₁ x₂) (boolrecₙ ())
  αneRedTerm (boolrec-false x x₁ x₂) (boolrecₙ ())
  αneRedTerm (α-subst d) (αₙ-base Truezero tε) = whnfRedTerm d zeroₙ
  αneRedTerm (α-subst d) (αₙ-base (Truesuc k) tε) = whnfRedTerm d sucₙ
  αneRedTerm (α-subst d) (αₙ-rec d') = αneRedTerm d d'
  αneRedTerm (α-red ⊢n inl) (αₙ-rec n) = NotTrueNatαNe _ (InLConTrueNat _ _ _ inl) n -- NotTrueNatαNe _ (TrueNatToTerm _ _) n
  αneRedTerm {lε =  ⊢ₗ• l lε n b nε} (α-red ⊢n inl) (αₙ-base t (NotInThere l notinl n b notn)) = NotInLConNotInLCon _ _ (addₗ n b l) (NotInThere _ notinl _ _ notn) inl
  
  neRedTerm : (d : Γ / lε ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
  neRedTerm (conv d x) n = neRedTerm d n
  neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
  neRedTerm (β-red x x₁ x₂) (∘ₙ ())
  neRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = neRedTerm d n₁
  neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
  neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
  neRedTerm (Emptyrec-subst x d) (Emptyrecₙ n₁) = neRedTerm d n₁
  neRedTerm (fst-subst _ _ d) (fstₙ n) = neRedTerm d n
  neRedTerm (snd-subst _ _ d) (sndₙ n) = neRedTerm d n
  neRedTerm (Σ-β₁ F G x x₁) (fstₙ ())
  neRedTerm (Σ-β₂ F G x x₁) (sndₙ ())
  neRedTerm (boolrec-subst x x₁ x₂ d) (boolrecₙ b₁) = neRedTerm d b₁
  neRedTerm (boolrec-true x x₁ x₂) (boolrecₙ ())
  neRedTerm (boolrec-false x x₁ x₂) (boolrecₙ ())
  neRedTerm (α-subst d) (αₙ cnen) = ContainsNeRedTerm d cnen
  neRedTerm (α-red ⊢n inl) (αₙ n) = TrueNat≢Cne n (InLConTrueNat _ _ _ inl) -- TrueNat≢Cne n (TrueNatToTerm _ _)
  
  ContainsNeRedTerm : (d : Γ / lε ⊢ t ⇒ u ∷ A) (n : ContainsNeutral t) → ⊥
  ContainsNeRedTerm d (ncontn neT) = neRedTerm d neT
  ContainsNeRedTerm d (Scontn n) = whnfRedTerm d sucₙ
  
  whnfRedTerm : ∀ {l : LCon} {lε : ⊢ₗ l} → (d : Γ / lε ⊢ t ⇒ u ∷ A) (w : Whnf {l} {lε} t) → ⊥
  whnfRedTerm (conv d x) w = whnfRedTerm d w
  whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
  whnfRedTerm (β-red x x₁ x₂) (ne (∘ₙ ()))
  whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
  whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
  whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
  whnfRedTerm (Emptyrec-subst x d) (ne (Emptyrecₙ x₂)) = neRedTerm d x₂
  whnfRedTerm (fst-subst _ _ d) (ne (fstₙ n)) = neRedTerm d n
  whnfRedTerm (snd-subst _ _ d) (ne (sndₙ n)) = neRedTerm d n
  whnfRedTerm (Σ-β₁ F G x x₁) (ne (fstₙ ()))
  whnfRedTerm (Σ-β₂ F G x x₁) (ne (sndₙ ()))
  whnfRedTerm (boolrec-subst x x₁ x₂ d) (ne (boolrecₙ b)) = neRedTerm d b
  whnfRedTerm (boolrec-true x x₁ x₂) (ne (boolrecₙ ()))
  whnfRedTerm (boolrec-false x x₁ x₂) (ne (boolrecₙ ()))
  whnfRedTerm d (αₙ αn) = αneRedTerm d αn
  whnfRedTerm (α-subst d) (ne (αₙ cnet)) = ContainsNeRedTerm d cnet
  whnfRedTerm (α-red ⊢n inl) (ne (αₙ cnet)) = TrueNat≢Cne cnet (InLConTrueNat _ _ _ inl) -- TrueNat≢Cne cnet (TrueNatToTerm _ _)
    
neRed : (d : Γ / lε ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce


whnfRed : (d : Γ / lε ⊢ A ⇒ B) (w : Whnf {l} {lε} A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : (d : Γ / lε ⊢ t ⇒* u ∷ A) (w : Whnf {l} {lε} t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) Σₙ = PE.refl
whnfRed*Term (id x) ℕₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) Unitₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) prodₙ = PE.refl
whnfRed*Term (id x) zeroₙ = PE.refl
whnfRed*Term (id x) sucₙ = PE.refl
whnfRed*Term (id x) starₙ = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)
whnfRed*Term (id x) 𝔹ₙ = PE.refl
whnfRed*Term (id x) trueₙ = PE.refl
whnfRed*Term (id x) falseₙ = PE.refl
whnfRed*Term (id d) (αₙ αn) = PE.refl
whnfRed*Term (x ⇨ d) (αₙ αn) = ⊥-elim (αneRedTerm x αn)

whnfRed* : (d : Γ / lε ⊢ A ⇒* B) (w : Whnf {l} {lε} A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic
  
whrDetTerm : ∀ {l t u u′ A A′} {lε : ⊢ₗ l} (d : Γ / lε ⊢ t ⇒ u ∷ A) (d′ : Γ / lε ⊢ t ⇒ u′ ∷ A′) → u PE.≡ u′
whrDetTerm  (conv d x) d′ = whrDetTerm  d d′
whrDetTerm  d (conv d′ x₁) = whrDetTerm  d d′
whrDetTerm  (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm  d d′ = PE.refl
whrDetTerm  (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
whrDetTerm  (fst-subst _ _ x) (fst-subst _ _ y) rewrite whrDetTerm  x y = PE.refl
whrDetTerm  (snd-subst _ _ x) (snd-subst _ _ y) rewrite whrDetTerm  x y = PE.refl
whrDetTerm  (Σ-β₁ F G x x₁) (Σ-β₁ F₁ G₁ x₂ x₃) = PE.refl
whrDetTerm  (Σ-β₂ F G x x₁) (Σ-β₂ F₁ G₁ x₂ x₃) = PE.refl
whrDetTerm  (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm  d d′ = PE.refl
whrDetTerm  (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm  (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm  (Emptyrec-subst x d) (Emptyrec-subst x₂ d′) rewrite whrDetTerm  d d′ = PE.refl
whrDetTerm  (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm  (β-red x x₁ x₂) (app-subst d x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm  (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm  (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm  (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm  (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm  (fst-subst _ _ x) (Σ-β₁ F G x₁ x₂) = ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm  (snd-subst _ _ x) (Σ-β₂ F G x₁ x₂) = ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm  (Σ-β₁ F G x x₁) (fst-subst _ _ y) = ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm  (Σ-β₂ F G x x₁) (snd-subst _ _ y) = ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm  (boolrec-subst x x₁ x₂ d) (boolrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm  d d′ = PE.refl
whrDetTerm  (boolrec-subst x x₁ x₂ d) (boolrec-true x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d trueₙ)
whrDetTerm  (boolrec-subst x x₁ x₂ d) (boolrec-false x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d falseₙ)
whrDetTerm  (boolrec-true x x₁ x₂) (boolrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ trueₙ)
whrDetTerm  (boolrec-false x x₁ x₂) (boolrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ falseₙ)
whrDetTerm  (boolrec-true x x₁ x₂) (boolrec-true x₃ x₄ x₅) = PE.refl
whrDetTerm  (boolrec-false x x₁ x₂) (boolrec-false x₃ x₄ x₅) = PE.refl
whrDetTerm  (α-subst d) (α-subst d′) rewrite whrDetTerm  d d′ = PE.refl
whrDetTerm {lε = ⊢ₗ• l lε n b nε} (α-red ⊢n (InHere _ _ t=m u=b _)) (α-red ⊢n' (InHere _ _ t=m' u=b' _)) = PE.trans u=b (PE.sym u=b')
whrDetTerm {lε = ⊢ₗ• l lε n b nε} (α-red ⊢n (InHere _ _ t=m u=b _)) (α-red ⊢n' (InThere _ inl' _ _)) = ⊥-elim (NotInLConNotInLCon _ _ _ (NotInLConNatNotInLCon _ _ _ nε t=m) inl')
whrDetTerm {lε = ⊢ₗ• l lε n b nε} (α-red ⊢n' (InThere _ inl' _ _))  (α-red ⊢n (InHere _ _ t=m u=b _)) = ⊥-elim (NotInLConNotInLCon _ _ _ (NotInLConNatNotInLCon _ _ _ nε t=m) inl')
whrDetTerm {lε = ⊢ₗ• l lε n b nε} (α-red ⊢n (InThere _ inl _ _)) (α-red ⊢n' (InThere  _ inl' _ _)) = InLConUnique _ _ _ _ lε inl inl'
whrDetTerm {l = addₗ m b l}  (α-red ⊢n inl) (α-subst d′)  =  ⊥-elim (whnfRedTerm d′ (naturalWhnf (TrueNatNatural (InLConTrueNat _ _ _ inl))))
whrDetTerm {l = addₗ m b l} (α-subst d′) (α-red ⊢n inl) = ⊥-elim (whnfRedTerm d′ (naturalWhnf (TrueNatNatural (InLConTrueNat _ _ _ inl))))


whrDet : (d : Γ / lε ⊢ A ⇒ B) (d′ : Γ / lε ⊢ A ⇒ B′) → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : (d : Γ / lε ⊢ t ↘ u ∷ A) (d′ : Γ / lε ⊢ t ⇒* u′ ∷ A) → Γ / lε ⊢ u′ ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ / _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : (d : Γ / lε ⊢ t ↘ u ∷ A) (d′ : Γ / lε ⊢ t ↘ u′ ∷ A) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ / _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : (d : Γ / lε ⊢ A ↘ B) (d′ : Γ / lε ⊢ A ↘ B′) → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ / _ ⊢ x ↘ _)
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Identity of syntactic reduction

idRed:*: : Γ / lε ⊢ A → Γ / lε ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : Γ / lε ⊢ t ∷ A → Γ / lε ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : ∀ {l} {lε : ⊢ₗ l} → Γ / lε ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U
UnotInA (ϝⱼ g d) = UnotInA g
  
UnotInA[t] : ∀ {l} {lε : ⊢ₗ l} → t [ a ] PE.≡ U
         → Γ / lε ⊢ a ∷ A
         → Γ ∙ A / lε ⊢ t ∷ B
         → ⊥
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ x₂ x₃)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂
UnotInA[t] t≡u ⊢a (ϝⱼ g d) = UnotInA[t] t≡u (τTerm _ _ _ _ ⊢a) g -- UnotInA[t] t≡u (τTerm _ _ _ ⊢a) g

  
redU*Term′ : U′ PE.≡ U → Γ / lε ⊢ A ⇒ U′ ∷ B → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ PE.refl (natrec-zero x x₁ x₂) = UnotInA x₁
redU*Term′ () (natrec-suc x x₁ x₂ x₃)
redU*Term′ () (Emptyrec-subst x A⇒U)
redU*Term′ PE.refl (Σ-β₁ F G x x₁) = UnotInA x
redU*Term′ PE.refl (Σ-β₂ F G x x₁) = UnotInA x₁
redU*Term′ PE.refl (boolrec-true x₁ x₂ x₃) = UnotInA x₂
redU*Term′ PE.refl (boolrec-false x₁ x₂ x₃) = UnotInA x₃
redU*Term′ PE.refl (α-red ⊢n k) = TrueBool≢U (InLConTrueBool _ _ _ k)
  
redU*Term : Γ / lε ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : Γ / lε ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : Γ / lε ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)
