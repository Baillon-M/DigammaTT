{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape as ES

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : LCon
    lε : ⊢ₗ l

-- Reflexivity of reducible types.
reflEq : ∀ {k A} ([A] : Γ / lε ⊩⟨ k ⟩ A) → Γ / lε ⊩⟨ k ⟩ A ≡ A / [A]
reflEq [A] = reflEqAux [A] (idRed:*: (escape [A]))

mutual

  reflNatural-prop : ∀ {n}
                   → Natural-prop Γ lε n
                   → [Natural]-prop Γ lε n n
  reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
    sucᵣ (ℕₜ₌ n n d d t≡t
              (reflNatural-prop prop))
  reflNatural-prop zeroᵣ = zeroᵣ
  reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)
  -- reflNatural-prop (ne (neNfϝ {[A]t = [A]t} ⊢k αk tk fk)) =
  --  PE.⊥-elim (ℕ≢ne (_/_⊩ne_.neK [A]t) (whnfRed* (red (_/_⊩ne_.D [A]t)) ℕₙ))
  --reflNatural-prop (ℕϝ ⊢n αn (ℕₜ k red k=k prop) (ℕₜ k' red' k'=k' prop')) = ?
    --[ℕ]ϝ-l αn (ℕϝ ⊢n αn (ℕₜ k red k=k prop) (ℕₜ k' red' k'=k' prop'))
    --     (ℕₜ₌ _ _ red red k=k (reflNatural-prop prop))
    --     (ℕₜ₌ _ _ red' red' k'=k' (reflNatural-prop prop'))
  reflEqTermℕ : ∀ {n}
           → Γ / lε ⊩ℕ n ∷ℕ
           → Γ / lε ⊩ℕ n ≡ n ∷ℕ
  reflEqTermℕ (ℕₜ n d t≡t prop) = ℕₜ₌ n n d d t≡t (reflNatural-prop prop)
  
reflBoolean-prop : ∀ {n}
                 → Boolean-prop Γ lε n
                 → [Boolean]-prop Γ lε n n
reflBoolean-prop trueᵣ = trueᵣ
reflBoolean-prop falseᵣ = falseᵣ
reflBoolean-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)
-- reflBoolean-prop (ne (neNfϝ {[A]t = [A]t} ⊢k αk tk fk)) =
--  PE.⊥-elim (𝔹≢ne (_/_⊩ne_.neK [A]t) (whnfRed* (red (_/_⊩ne_.D [A]t)) 𝔹ₙ))
-- reflBoolean-prop (𝔹ϝ ⊢n αn (𝔹ₜ k red k=k prop) (𝔹ₜ k' red' k'=k' prop')) = ?
--  [𝔹]ϝ-l αn (𝔹ϝ ⊢n αn (𝔹ₜ k red k=k prop) (𝔹ₜ k' red' k'=k' prop'))
--         (𝔹ₜ₌ _ _ red red k=k (reflBoolean-prop prop))
--         (𝔹ₜ₌ _ _ red' red' k'=k' (reflBoolean-prop prop'))
reflEqTerm𝔹 : ∀ {n}
           → Γ / lε ⊩𝔹 n ∷𝔹
           → Γ / lε ⊩𝔹 n ≡ n ∷𝔹
reflEqTerm𝔹 (𝔹ₜ n d t≡t prop) = 𝔹ₜ₌ n n d d t≡t (reflBoolean-prop prop)

-- reflEmpty-prop : ∀ {n}
--                 → Empty-prop Γ lε n
--                 → [Empty]-prop Γ lε n n
-- reflEmpty-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {k A t} ([A] : Γ / lε ⊩⟨ k ⟩ A)
           → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
           → Γ / lε ⊩⟨ k ⟩ t ≡ t ∷ A / [A]
reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ ⊢t t≡t [A]) =
  Uₜ₌ ⊢t ⊢t t≡t [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) ⊢t = reflEqTermℕ ⊢t
reflEqTerm (𝔹ᵣ D) ⊢t = reflEqTerm𝔹 ⊢t
-- reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
--  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
--    (reflEmpty-prop prop)
-- reflEqTerm (Unitᵣ D) (Unitₜ n [ ⊢t , ⊢u , d ] prop) =
--   Unitₜ₌ ⊢t ⊢t
reflEqTerm {k = k} (ne neA) [t] = LogRel.reflEqTermNe k (logRelRec _) neA [t]
reflEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Πₜ ⊢ff f≡f [f] [f]₁) =
  Πₜ₌ f≡f [t] [t]
    (λ [ρ] ≤ε lε' N<s ⊢Δ [a] ≤ε' lε'' M<s →
      [f] [ρ] ≤ε lε' N<s ⊢Δ [a] [a] (reflEqTerm (proj₂ ([F] [ρ]) ≤ε lε' N<s ⊢Δ) [a]) ≤ε' lε'' M<s) 
reflEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d pProd p≅p [prop]) =
  Σₜ₌ p p d d pProd pProd p≅p [t] [t] λ ≤ε lε' N<s →
    let [fst] , [snd] = [prop] ≤ε lε' N<s
    in [fst] , ([fst] , (reflEqTerm (proj₂ ([F] id) ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F))) [fst] ,
      λ ≤ε' lε'' M<s → reflEqTerm (proj₂ ([G] id ≤ε lε' N<s (Con≤ ≤ε (wf ⊢F)) (proj₁ ([prop] ≤ε lε' N<s))) ≤ε' lε'' M<s)
                                  ([snd] ≤ε' lε'' M<s)))
    -- (reflEqTerm ([F] id (wf ⊢F)) [fst])
    -- (reflEqTerm ([G] id (wf ⊢F) [fst]) [snd])
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
