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

reflNatural-prop : ∀ {n}
                 → Natural-prop Γ lε n
                 → [Natural]-prop Γ lε n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)
reflNatural-prop (ℕϝ ⊢n αn (ℕₜ k red k=k prop) (ℕₜ k' red' k'=k' prop')) =
  [ℕ]ϝ-l αn (ℕϝ ⊢n αn (ℕₜ k red k=k prop) (ℕₜ k' red' k'=k' prop'))
       (ℕₜ₌ _ _ red red k=k (reflNatural-prop prop))
       (ℕₜ₌ _ _ red' red' k'=k' (reflNatural-prop prop'))

reflBoolean-prop : ∀ {n}
                 → Boolean-prop Γ lε n
                 → [Boolean]-prop Γ lε n n
reflBoolean-prop trueᵣ = trueᵣ
reflBoolean-prop falseᵣ = falseᵣ
reflBoolean-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)
reflBoolean-prop (𝔹ϝ ⊢n αn (𝔹ₜ k red k=k prop) (𝔹ₜ k' red' k'=k' prop')) =
  [𝔹]ϝ-l αn (𝔹ϝ ⊢n αn (𝔹ₜ k red k=k prop) (𝔹ₜ k' red' k'=k' prop'))
         (𝔹ₜ₌ _ _ red red k=k (reflBoolean-prop prop))
         (𝔹ₜ₌ _ _ red' red' k'=k' (reflBoolean-prop prop'))


-- reflEmpty-prop : ∀ {n}
--                 → Empty-prop Γ lε n
--                 → [Empty]-prop Γ lε n n
-- reflEmpty-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {k A t} ([A] : Γ / lε ⊩⟨ k ⟩ A)
           → Γ / lε ⊩⟨ k ⟩ t ∷ A / [A]
           → Γ / lε ⊩⟨ k ⟩ t ≡ t ∷ A / [A]
reflEqTerm (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
  Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A])
reflEqTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop)
reflEqTerm (𝔹ᵣ D) (𝔹ₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  𝔹ₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflBoolean-prop prop)
-- reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
--  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
--    (reflEmpty-prop prop)
-- reflEqTerm (Unitᵣ D) (Unitₜ n [ ⊢t , ⊢u , d ] prop) =
--   Unitₜ₌ ⊢t ⊢t
reflEqTerm (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f [t] [t]
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t]@(Σₜ p d pProd p≅p [fst] [snd]) =
  Σₜ₌ p p d d pProd pProd p≅p [t] [t] [fst] [fst]
    (reflEqTerm ([F] id (wf ⊢F)) [fst])
    (reflEqTerm ([G] id (wf ⊢F) [fst]) [snd])
reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
reflEqTerm (ϝᵣ mε ([ ⊢A , ⊢B , D ]) αB tA fA) ( x , y ) = reflEqTerm tA x , reflEqTerm fA y 
