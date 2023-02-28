{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeViewTest2 {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
import Definition.Typed.Weakening as Wk
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.ShapeView

open import Tools.Nat
open import Tools.Unit
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.Sum as TS
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B : Term n
    l : LCon
    lε : ⊢ₗ l

                                    

mutual 
  -- A view for constructor equality of types where embeddings are ignored

  ϝShapeViewWHelperDom :
    ∀ {Γ l} {lε : ⊢ₗ l} {m} {mε : NotInLConNat m l} {k k′ k″}
      {i} {l' : LCon} {lε″ : ⊢ₗ l'} {ρ : Wk i n} {Δ : Con Term i} F 
       ([F] : ∀ {i} {l′ : LCon} {≤ε : l  ≤ₗ l′} {lε′ : ⊢ₗ l′} {ρ : Wk i n} {Δ : Con Term i}
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε′ → Δ / lε′ ⊩⟨ k ⟩ wk ρ F)
       ([tF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Btrue l) ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k′ ⟩ wk ρ F)
       ([fF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Bfalse l)  ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k″ ⟩ wk ρ F)
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″
         → (f< : l ≤ₗ l')
         → (((InLConNat m Btrue l') TS.⊎ (InLConNat m Bfalse l')) TS.⊎ (NotInLConNat m l'))
         → Set
  ϝShapeViewWHelperDom {m = m} {l' = l'} {Δ = Δ} F [F] [tF] [fF] [ρ] ⊢Δ f< (TS.inj₁ (TS.inj₁ inl)) =
    ⊤ -- DShapeView Δ (≤ₗ-id _) _ _ (wk _ F) (wk _ F) ([F] {≤ε = f<} [ρ] ⊢Δ) ([tF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ)
  ϝShapeViewWHelperDom {l' = l'} {Δ = Δ} F [F] [tF] [fF] [ρ] ⊢Δ f< (TS.inj₁ (TS.inj₂ inl)) =
    ⊤ -- DShapeView Δ (≤ₗ-id _) _ _ (wk _ F) (wk _ F) ([F] {≤ε = f<} [ρ] ⊢Δ) ([fF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ)
  ϝShapeViewWHelperDom {l' = l'} {Δ = Δ} F [F] [tF] [fF] [ρ] ⊢Δ f< (TS.inj₂ notinl') =
    ϝShapeView Δ {mε = notinl'} _ _ _ (wk _ F)
      ([F] {≤ε = f<} [ρ] ⊢Δ)
      ([tF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ] (τCon _ _ _ _ ⊢Δ))
      ([fF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ] (τCon _ _ _ _ ⊢Δ))
    

  data ϝShapeView (Γ : Con Term n) :
    ∀ {l : LCon} {lε : ⊢ₗ l} {m mε} k k′ k″ A
         ([A] : Γ / lε ⊩⟨ k ⟩ A)
         ([A]t : Γ / ⊢ₗ• l lε m Btrue mε ⊩⟨ k′ ⟩ A)
         ([A]f : Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ A)
      → Set where
    Uᵥ : ∀ {l lε m mε k k′ k″} UA UAt UAf → ϝShapeView Γ {l} {lε} {m} {mε} k k′ k″ U (Uᵣ UA) (Uᵣ UAt) (Uᵣ UAf)
    Bᵥ : ∀ {l lε m mε} {k k′ k″ : TypeLevel} {A} W F G D tD fD ⊢F t⊢F f⊢F ⊢G t⊢G f⊢G A≡A tA≡A fA≡A
       ([F] : ∀ {i} {l′ : LCon} {≤ε : l  ≤ₗ l′} {lε′ : ⊢ₗ l′} {ρ : Wk i n} {Δ : Con Term i}
              → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε′ → Δ / lε′ ⊩⟨ k ⟩ wk ρ F)
       ([tF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Btrue l) ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k′ ⟩ wk ρ F)
       ([fF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Bfalse l)  ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
         → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k″ ⟩ wk ρ F)
       ([G] : ∀ {m} {ρ} {Δ} {a : Term m} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k ⟩ a ∷ (wk ρ F) / [F] {_} {l′} {≤ε} [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ])
       ([tG] : ∀ {i} {ρ} {Δ} {a : Term i} {l′ : LCon} {≤ε : (addₗ m Btrue l)  ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k′ ⟩ a ∷ (wk ρ F) / [tF] {_} {l′} {≤ε} [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G [ a ])
       ([fG] : ∀ {i} {ρ} {Δ} {a : Term i} {l′ : LCon} {≤ε : (addₗ m Bfalse l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k″ ⟩ a ∷ (wk ρ F) / [fF] {_} {l′} {≤ε} [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k″ ⟩ wk (lift ρ) G [ a ])
       (G-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → ([a] : Δ / lε′ ⊩⟨ k ⟩ a ∷ wk ρ F / [F] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → ([b] : Δ / lε′ ⊩⟨ k ⟩ b ∷ wk ρ F / [F] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k a b (wk ρ F) ([F] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a])
       (tG-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : (addₗ m Btrue l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → ([a] : Δ / lε′ ⊩⟨ k′ ⟩ a ∷ wk ρ F / [tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → ([b] : Δ / lε′ ⊩⟨ k′ ⟩ b ∷ wk ρ F / [tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k′ a b (wk ρ F) ([tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [tG] [ρ] ⊢Δ [a])
       (fG-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : (addₗ m Bfalse l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → ([a] : Δ / lε′ ⊩⟨ k″ ⟩ a ∷ wk ρ F / [fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → ([b] : Δ / lε′ ⊩⟨ k″ ⟩ b ∷ wk ρ F / [fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k″ a b (wk ρ F) ([fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
              → Δ / lε′ ⊩⟨ k″ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [fG] [ρ] ⊢Δ [a])
       → (∀ {i} {l' : LCon} {lε″ : ⊢ₗ l'} {ρ : Wk i n} {Δ : Con Term i} [ρ] ⊢Δ (f< : l ≤ₗ l') isinl
         → ϝShapeViewWHelperDom {lε = lε} {mε = mε} {i = i} {lε″ = lε″} {ρ = ρ} {Δ = Δ} F
                                (λ {m} {_} {≤ε} → [F] {≤ε = ≤ε})
                                (λ {m} {_} {≤ε} → [tF] {≤ε = ≤ε})
                                (λ {m} {_} {≤ε} → [fF] {≤ε = ≤ε}) [ρ] ⊢Δ f< isinl)
       → ϝShapeView Γ {l} {lε} {m} {mε} k k′ k″ A (Bᵣ′ W F G D ⊢F ⊢G A≡A (λ {m} {_} {≤ε} → [F] {≤ε = ≤ε}) [G] G-ext)
                                                  (Bᵣ′ W F G tD t⊢F t⊢G tA≡A (λ {m} {_} {≤ε} → [tF] {≤ε = ≤ε}) [tG] tG-ext)
                                                  (Bᵣ′ W F G fD f⊢F f⊢G fA≡A (λ {m} {_} {≤ε} → [fF] {≤ε = ≤ε}) [fG] fG-ext)
         

  data DShapeView (Γ : Con Term n) :
    ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l') k k′ A B
         (p : Γ / lε ⊩⟨ k ⟩ A) (q : Γ / lε' ⊩⟨ k′ ⟩ B)
      → Set where
    Uᵥ : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {k k′} UA UB → DShapeView Γ {l} {l'} {lε} {lε'} f< k k′ U U (Uᵣ UA) (Uᵣ UB)
    ℕᵥ : ∀ {l} {l'} {lε} {lε'} {f< :  l ≤ₗ l'} {A B k k′} ℕA ℕB → DShapeView Γ {l} {l'} {lε} {lε'} f< k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
    𝔹ᵥ : ∀ {l} {l'} {lε} {lε'} {f< :  l ≤ₗ l'} {A B k k′} 𝔹A 𝔹B → DShapeView Γ {l} {l'} {lε} {lε'} f< k k′ A B (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B)
    ne  : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {A B k k′} neA neB
        → DShapeView Γ {l} {l'} {lε} {lε'} f< k k′ A B (ne neA) (ne neB)
    Bᵥ : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {A B k k′} W F F' G G' D D' ⊢F ⊢F' ⊢G ⊢G' A≡A B≡B
       ([F] : ∀ {m} {l′ : LCon} {≤ε : l  ≤ₗ l′} {lε′ : ⊢ₗ l′} {ρ : Wk m n} {Δ : Con Term m} → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε′ → Δ / lε′ ⊩⟨ k ⟩ wk ρ F)
         ([F'] : ∀ {m} {l″ : LCon} {≤ε : l'  ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk m n} {Δ : Con Term m} → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k′ ⟩ wk ρ F')
       ([G] : ∀ {m} {ρ} {Δ} {a : Term m} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k ⟩ a ∷ (wk ρ F) / [F] {_} {l′} {≤ε} [ρ] ⊢Δ
              → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ])
       ([G'] : ∀ {m} {ρ} {Δ} {a : Term m} {l′ : LCon} {≤ε : l' ≤ₗ l′} {lε′ : ⊢ₗ l′}
               [ρ] ⊢Δ
             → Δ / lε′ ⊩⟨ k′ ⟩ a ∷ (wk ρ F') / [F'] {_} {l′} {≤ε} [ρ] ⊢Δ
             → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G' [ a ])
       (G-ext : ∀ {m} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
                [ρ] ⊢Δ
              → ([a] : Δ / lε′ ⊩⟨ k ⟩ a ∷ wk ρ F / [F] {m} {l′} {≤ε} [ρ] ⊢Δ)
              → ([b] : Δ / lε′ ⊩⟨ k ⟩ b ∷ wk ρ F / [F] {m} {l′} {≤ε} [ρ] ⊢Δ)
              → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k a b (wk ρ F) ([F] {m} {l′} {≤ε} [ρ] ⊢Δ)
              → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a])
       (G-ext' : ∀ {m} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : l' ≤ₗ l′} {lε′ : ⊢ₗ l′}
                 [ρ] ⊢Δ
               → ([a] : Δ / lε′ ⊩⟨ k′ ⟩ a ∷ wk ρ F' / [F'] {m} {l′} {≤ε} [ρ] ⊢Δ)
               → ([b] : Δ / lε′ ⊩⟨ k′ ⟩ b ∷ wk ρ F' / [F'] {m} {l′} {≤ε} [ρ] ⊢Δ)
               → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k′ a b (wk ρ F') ([F'] {m} {l′} {≤ε} [ρ] ⊢Δ)
               → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G' [ a ] ≡ wk (lift ρ) G' [ b ] / [G'] [ρ] ⊢Δ [a])
       → (∀ {m} {l′ l″ : LCon} {≤ε : l  ≤ₗ l′} {≤ε' : l'  ≤ₗ l″} {≤ε′ : l′ ≤ₗ l″} {lε′ : ⊢ₗ l′} {lε″ : ⊢ₗ l″} {ρ : Wk m n} {Δ : Con Term m}
            ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ′ : ⊢ Δ / lε′) (⊢Δ″ : ⊢ Δ / lε″)
            → DShapeView Δ ≤ε′ k k′ (wk ρ F) (wk ρ F') ([F] {m} {l′} {≤ε = ≤ε} [ρ] ⊢Δ′) ([F'] {≤ε = ≤ε'} [ρ] ⊢Δ″))
         → (∀ {m} {l′ l″ : LCon} {≤ε : l  ≤ₗ l′} {≤ε' : l'  ≤ₗ l″} {≤ε′ : l′ ≤ₗ l″} {lε′ : ⊢ₗ l′} {lε″ : ⊢ₗ l″}
         {ρ : Wk m n} {Δ : Con Term m} {a}
           ([ρ] : ρ Wk.∷ Δ ⊆ Γ) (⊢Δ′ : ⊢ Δ / lε′) (⊢Δ″ : ⊢ Δ / lε″)
           → ([a] : Δ / lε′ ⊩⟨ k ⟩ a ∷ wk ρ F / [F] {m} {l′} {≤ε} [ρ] ⊢Δ′)
           → ([a'] : Δ / lε″ ⊩⟨ k′ ⟩ a ∷ wk ρ F' / [F'] {m} {l″} {≤ε'} [ρ] ⊢Δ″)
           → DShapeView Δ ≤ε′ k k′ (wk (lift ρ) G [ a ]) (wk (lift ρ) G' [ a ]) ([G] [ρ] ⊢Δ′ [a]) ([G'] [ρ] ⊢Δ″ [a']))
       → DShapeView Γ {l} {l'} {lε} {lε'} f< k k′ A B (Bᵣ′ W F G D ⊢F ⊢G A≡A (λ {m} {_} {≤ε} → [F] {≤ε = ≤ε}) [G] G-ext)
                                                  (Bᵣ′ W F' G' D' ⊢F' ⊢G' B≡B (λ {m} {_} {≤ε} → [F'] {≤ε = ≤ε}) [G'] G-ext')
    ϝᵣ-l₀ : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {n nε k k' A B} (f<' : (addₗ n Btrue l) ≤ₗ l') [B] [A]t [A]f
          → DShapeView Γ {_} {l'} {⊢ₗ• l lε n Btrue  nε} {lε'} f<' k k' A B [A]t [B]
          → DShapeView Γ {l} {l'} {lε} {lε'} f< k k' A B (ϝᵣ nε [A]t [A]f) [B]
    ϝᵣ-l₁ : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {n nε k k' A B} (f<' : (addₗ n Bfalse l) ≤ₗ l') [B] [A]t [A]f
          → DShapeView Γ {_} {l'} {⊢ₗ• l lε n Bfalse nε} {lε'} f<' k k' A B [A]f [B]
          → DShapeView Γ {l} {l'} {lε} {lε'} f< k k' A B (ϝᵣ nε [A]t [A]f) [B]
    ϝᵣ-l₂ : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {n nε nε' k k' k′ k″ A B}
            (f<-l : (addₗ n Btrue l) ≤ₗ (addₗ n Btrue l'))
            (f<-r : (addₗ n Bfalse l) ≤ₗ (addₗ n Bfalse l')) [B] [A]t [A]f [B]t [B]f
          → DShapeView Γ {_} {_} {⊢ₗ• l lε n Btrue  nε} {⊢ₗ• l' lε' n Btrue  nε'} f<-l k k′ A B [A]t [B]t
          → DShapeView Γ {_} {_} {⊢ₗ• l lε n Bfalse nε} {⊢ₗ• l' lε' n Bfalse nε'} f<-r k k″ A B [A]f [B]f
          → ϝShapeView Γ {l'} {lε'} {n} {nε'} k' k′ k″ B [B] [B]t [B]f
          → DShapeView Γ {l} {l'} {lε} {lε'} f< k k' A B (ϝᵣ nε [A]t [A]f) [B]
    ϝᵣ-r : ∀ {l l' lε lε'} {f< :  l ≤ₗ l'} {n nε k k' A B}
           (f<-l : l ≤ₗ (addₗ n Btrue l'))
           (f<-r : l ≤ₗ (addₗ n Bfalse l')) [A] [B]t [B]f
         → DShapeView Γ {l} {_} {lε} {⊢ₗ• l' lε' n Btrue  nε} f<-l k k' A B [A] [B]t
         → DShapeView Γ {l} {_} {lε} {⊢ₗ• l' lε' n Bfalse nε} f<-r k k' A B [A] [B]f
         → DShapeView Γ {l} {l'} {lε} {lε'} f< k k' A B [A] (ϝᵣ nε [B]t [B]f)
    emb⁰¹ : ∀ {l} {l'} {lε} {lε'} {f< :  l ≤ₗ l'} {A B k p q}
          → DShapeView Γ {l} {l'} {lε} {lε'} f< ⁰ k A B p q
          → DShapeView Γ {l} {l'} {lε} {lε'} f< ¹ k A B (emb 0<1 p) q
    emb¹⁰ : ∀ {l} {l'} {lε} {lε'} {f< :  l ≤ₗ l'} {A B k p q}
          → DShapeView Γ {l} {l'} {lε} {lε'} f< k ⁰ A B p q
          → DShapeView Γ {l} {l'} {lε} {lε'} f< k ¹ A B p (emb 0<1 q)

mutual 
  GoodCases : ∀ {A k k′ l l'} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
                ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε' ⊩⟨ k′ ⟩ A)
                → ShapeView Γ k k′ A A (TyLog≤ ≤ε [A]) [B] (reflEq (TyLog≤ ≤ε [A]))
                → DShapeView Γ ≤ε k k′ A A [A] [B]
  GoodCases f< (ℕᵣ [A]) (ℕᵣ ℕB) Shp = ℕᵥ [A] ℕB
  GoodCases f< (𝔹ᵣ [A]) (𝔹ᵣ 𝔹B) Shp = 𝔹ᵥ [A] 𝔹B
  GoodCases f< (Uᵣ [A]) (Uᵣ UB) Shp = Uᵥ [A] UB
  GoodCases f< (ne neA) (ne neB) Shp = ne neA neB
  GoodCases ≤ε (emb 0<1 [A]) [B] Shp =
    emb⁰¹ (GoodCases ≤ε [A] [B] (goodCasesRefl _ _))
  GoodCases ≤ε [A] (emb 0<1 [B]) Shp = emb¹⁰ (GoodCases ≤ε [A] [B] (goodCasesRefl _ _))
  GoodCases f< [A] (ϝᵣ mε [B]t [B]f) Shp =
    ϝᵣ-r (≤ₗ-add-r f<) (≤ₗ-add-r f<) [A] [B]t [B]f
      (GoodCases (≤ₗ-add-r f<) [A] [B]t (goodCasesRefl _ _))
      (GoodCases (≤ₗ-add-r f<) [A] [B]f (goodCasesRefl _ _))
  GoodCases {l' = l'} f< (ϝᵣ {m = m} mε [A]t [A]f) [B] Shp
    with decidInLConNat l' m
  GoodCases {l' = l'} f< (ϝᵣ {m = m} mε [A]t [A]f) [B] Shp
    | TS.inj₁ (TS.inj₁ inl) = 
      ϝᵣ-l₀ (≤ₗ-add _ _ _ f< inl) [B] [A]t [A]f (GoodCases (≤ₗ-add _ _ _ f< inl) [A]t [B] (goodCasesRefl _ _))
  GoodCases {l' = l'} f< (ϝᵣ {m = m} mε [A]t [A]f) [B] Shp
    | TS.inj₁ (TS.inj₂ inl) =
      ϝᵣ-l₁ (≤ₗ-add _ _ _ f< inl) [B] [A]t [A]f (GoodCases (≤ₗ-add _ _ _ f< inl) [A]f [B] (goodCasesRefl _ _))
  GoodCases {l' = l'} f< (ϝᵣ {m = m} mε [A]t [A]f) [B] Shp
    | TS.inj₂ notinl =
    ϝᵣ-l₂ {nε' = notinl}
    (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _))
    (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [B] [A]t [A]f (τTyLog [B]) (τTyLog [B])
    (GoodCases (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [A]t (τTyLog [B]) (goodCasesRefl _ _))
    (GoodCases (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [A]f (τTyLog [B]) (goodCasesRefl _ _))
    (ϝGC _ [B] (τTyLog [B]) (τTyLog [B]) (≤-refl _) (goodCasesRefl _ _) (goodCasesRefl _ _))
   -- ϝᵣ-l₂ {nε' = notinl}
   --       (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _))
   --       (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [B] [A]t [A]f (τTyLog [B]) (τTyLog [B])
   --       (GoodCases (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [A]t (τTyLog [B]) (goodCasesRefl _ _))
   --       (GoodCases (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) [A]f (τTyLog [B]) (goodCasesRefl _ _))
   --                  (ϝGC _ [B] (τTyLog [B]) (τTyLog [B]) (≤-refl _) (goodCasesRefl _ _)
   --                     (goodCasesRefl _ _))
  GoodCases f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') Shp
                 with whrDet* (Red≤* f< (red D) , Πₙ) (red D' , Πₙ)
  GoodCases f< (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bᵣ′ BΠ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') Shp
                 | PE.refl =
                 Bᵥ BΠ F F' G G' D D' ⊢F ⊢F' ⊢G ⊢G' A≡A A≡A' [F] [F'] [G] [G'] G-ext G-ext'
                 (λ {m} {l} {l'} {≤ε} {≤ε'} {≤ε′} {lε} {lε'} {ρ} {Δ} [ρ] ⊢Δ ⊢Δ′ →
                   GoodCases ≤ε′ ([F] [ρ] ⊢Δ) ([F'] [ρ] ⊢Δ′) (goodCasesRefl _ _))
                 (λ {m} {l} {l'} {≤ε} {≤ε'} {≤ε′} {lε} {lε'} {ρ} {Δ} {a} [ρ] ⊢Δ ⊢Δ′ [a] [a'] →
                    GoodCases _ ([G] [ρ] ⊢Δ [a]) ([G'] [ρ] ⊢Δ′ [a']) (goodCasesRefl _ _))
  GoodCases f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') Shp
                 with whrDet* (Red≤* f< (red D) , Σₙ) (red D' , Σₙ)
  GoodCases f< (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Bᵣ′ BΣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext') Shp
                 | PE.refl =
                 Bᵥ BΣ F F' G G' D D' ⊢F ⊢F' ⊢G ⊢G' A≡A A≡A' [F] [F'] [G] [G'] G-ext G-ext'
                 (λ {m} {l} {l'} {≤ε} {≤ε'} {≤ε′} {lε} {lε'} {ρ} {Δ} [ρ] ⊢Δ ⊢Δ′ →
                   GoodCases ≤ε′ ([F] [ρ] ⊢Δ) ([F'] [ρ] ⊢Δ′) (goodCasesRefl _ _))
                 (λ {m} {l} {l'} {≤ε} {≤ε'} {≤ε′} {lε} {lε'} {ρ} {Δ} {a} [ρ] ⊢Δ ⊢Δ′ [a] [a'] →
                    GoodCases _ ([G] [ρ] ⊢Δ [a]) ([G'] [ρ] ⊢Δ′ [a']) (goodCasesRefl _ _))

  ϝGC : ∀ {A k k′ k″ l m mε} {lε : ⊢ₗ l} (N : Nat)
                ([A] : Γ / lε ⊩⟨ k ⟩ A)
                ([A]t : Γ / ⊢ₗ• l lε m Btrue  mε ⊩⟨ k′ ⟩ A)
                ([A]f : Γ / ⊢ₗ• l lε m Bfalse mε ⊩⟨ k″ ⟩ A)
                → (((μTy [A]) + (μTy [A]t) + (μTy [A]f)) ≤ N)
                → ShapeView Γ k k′ A A (τTyLog [A]) [A]t (reflEq (τTyLog [A]))
                → ShapeView Γ k k″ A A (τTyLog [A]) [A]f (reflEq (τTyLog [A]))
                → ϝShapeView Γ k k′ k″ A [A] [A]t [A]f
  ϝGC {k = k} {m = m} {mε = mε} N BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
           (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
           (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
           N< (Bᵥ BΠ _ _ _) (Bᵥ BΠ _ _ _)
           with whrDet* ( red (τwfRed* D) , Πₙ) (red tD , Πₙ) 
           with whrDet* ( red (τwfRed* D) , Πₙ) (red fD , Πₙ)
  ϝGC {k = k} {m = m} {mε = mε} {lε = lε} N BA@(Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
           (Bᵣ′ BΠ tF tG tD t⊢F t⊢G tA≡A [tF] [tG] tG-ext)
           (Bᵣ′ BΠ fF fG fD f⊢F f⊢G fA≡A [fF] [fG] fG-ext)
           N< (Bᵥ BΠ _ _ _) (Bᵥ BΠ _ _ _)
           | PE.refl | PE.refl =
           Bᵥ BΠ F G D tD fD ⊢F t⊢F f⊢F ⊢G t⊢G f⊢G A≡A tA≡A fA≡A [F] [tF] [fF] [G] [tG] [fG] G-ext tG-ext fG-ext
           (λ {i : Nat} {l' : LCon} {lε″ : ⊢ₗ l'} {ρ} {Δ : Con Term i} ([ρ] : ρ Wk.∷ Δ ⊆ _) (⊢Δ : ⊢ Δ / lε″) (f< : _ ≤ₗ l') →
             λ { (TS.inj₁ (TS.inj₁ inl)) → tt; -- GoodCases (≤ₗ-id _) ([F] {≤ε = f<} [ρ] ⊢Δ)
                                             --        ([tF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ) (goodCasesRefl _ _) ;
                 (TS.inj₁ (TS.inj₂ inl)) → tt; -- GoodCases (≤ₗ-id _) ([F] {≤ε = f<} [ρ] ⊢Δ)
                                             --        ([fF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ) (goodCasesRefl _ _) ;
                 (TS.inj₂ notinl) → ϝGC _ ([F] {≤ε = f<} [ρ] ⊢Δ)
                                             ([tF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ]
                                               (τCon _ _ _ _ ⊢Δ))
                                             ([fF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ]
                                               (τCon _ _ _ _ ⊢Δ))
                                             (≤-refl _) (goodCasesRefl _ _) (goodCasesRefl _ _) })
  ϝGC N [A] [A]t [A]f N< tShp fShp = {!!}

--   ϝGCHelperDom : ∀ {l lε m mε} {k k′ k″ : TypeLevel} F G
--        ([F] : ∀ {i} {l′ : LCon} {≤ε : l  ≤ₗ l′} {lε′ : ⊢ₗ l′} {ρ : Wk i n} {Δ : Con Term i}
--               → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε′ → Δ / lε′ ⊩⟨ k ⟩ wk ρ F)
--        ([tF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Btrue l) ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
--          → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k′ ⟩ wk ρ F)
--        ([fF] : ∀ {i} {l″ : LCon} {≤ε : (addₗ m Bfalse l)  ≤ₗ l″} {lε″ : ⊢ₗ l″} {ρ : Wk i n} {Δ : Con Term i}
--          → ρ Wk.∷ Δ ⊆ Γ → ⊢ Δ / lε″ → Δ / lε″ ⊩⟨ k″ ⟩ wk ρ F)
--        ([G] : ∀ {m} {ρ} {Δ} {a : Term m} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k ⟩ a ∷ (wk ρ F) / [F] {_} {l′} {≤ε} [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ])
--        ([tG] : ∀ {i} {ρ} {Δ} {a : Term i} {l′ : LCon} {≤ε : (addₗ m Btrue l)  ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k′ ⟩ a ∷ (wk ρ F) / [tF] {_} {l′} {≤ε} [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G [ a ])
--        ([fG] : ∀ {i} {ρ} {Δ} {a : Term i} {l′ : LCon} {≤ε : (addₗ m Bfalse l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k″ ⟩ a ∷ (wk ρ F) / [fF] {_} {l′} {≤ε} [ρ] ⊢Δ
--               → Δ / lε′ ⊩⟨ k″ ⟩ wk (lift ρ) G [ a ])
--        (G-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : l ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → ([a] : Δ / lε′ ⊩⟨ k ⟩ a ∷ wk ρ F / [F] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → ([b] : Δ / lε′ ⊩⟨ k ⟩ b ∷ wk ρ F / [F] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k a b (wk ρ F) ([F] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → Δ / lε′ ⊩⟨ k ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [G] [ρ] ⊢Δ [a])
--        (tG-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : (addₗ m Btrue l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → ([a] : Δ / lε′ ⊩⟨ k′ ⟩ a ∷ wk ρ F / [tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → ([b] : Δ / lε′ ⊩⟨ k′ ⟩ b ∷ wk ρ F / [tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k′ a b (wk ρ F) ([tF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → Δ / lε′ ⊩⟨ k′ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [tG] [ρ] ⊢Δ [a])
--        (fG-ext : ∀ {i} {ρ} {Δ} {a b} {l′ : LCon} {≤ε : (addₗ m Bfalse l) ≤ₗ l′} {lε′ : ⊢ₗ l′}
--                 [ρ] ⊢Δ
--               → ([a] : Δ / lε′ ⊩⟨ k″ ⟩ a ∷ wk ρ F / [fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → ([b] : Δ / lε′ ⊩⟨ k″ ⟩ b ∷ wk ρ F / [fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → _/_⊩⟨_⟩_≡_∷_/_ Δ lε′ k″ a b (wk ρ F) ([fF] {i} {l′} {≤ε} [ρ] ⊢Δ)
--               → Δ / lε′ ⊩⟨ k″ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] / [fG] [ρ] ⊢Δ [a])
--        {i} {l' : LCon} {lε″ : ⊢ₗ l'} {ρ : Wk i n} {Δ : Con Term i} [ρ] ⊢Δ (f< : l ≤ₗ l')
--          → ϝShapeViewWHelperDom {lε = lε} {mε = mε} {i = i} {lε″ = lε″} {ρ = ρ} {Δ = Δ} F
--                                 (λ {m} {_} {≤ε} → [F] {≤ε = ≤ε})
--                                 (λ {m} {_} {≤ε} → [tF] {≤ε = ≤ε})
--                                 (λ {m} {_} {≤ε} → [fF] {≤ε = ≤ε}) [ρ] ⊢Δ f<
--   ϝGCHelperDom {m = m} F G [F] [tF] [fF] [G] [tG] [fG] G-ext tG-ext fG-ext {l' = l'} [ρ] ⊢Δ f<
--     with decidInLConNat l' m
--   ϝGCHelperDom {mε = mε} F G [F] [tF] [fF] [G] [tG] [fG] G-ext tG-ext fG-ext {l' = l'} [ρ] ⊢Δ f< 
--     | TS.inj₁ (TS.inj₁ inl) =
--     GoodCases (≤ₗ-id _) ([F] {≤ε = f<} [ρ] ⊢Δ) ([tF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ) (goodCasesRefl _ _)
--   ϝGCHelperDom {mε = mε} F G [F] [tF] [fF] [G] [tG] [fG] G-ext tG-ext fG-ext {l' = l'} [ρ] ⊢Δ f< 
--     | TS.inj₁ (TS.inj₂ inl) = 
--     GoodCases (≤ₗ-id _) ([F] {≤ε = f<} [ρ] ⊢Δ) ([fF] {≤ε = ≤ₗ-add _ _ _ f< inl} [ρ] ⊢Δ) (goodCasesRefl _ _)
--   ϝGCHelperDom {mε = mε} F G [F] [tF] [fF] [G] [tG] [fG] G-ext tG-ext fG-ext {l' = l'} [ρ] ⊢Δ f< 
--     | TS.inj₂ notinl' =
--     ϝGC _ ([F] {≤ε = f<} [ρ] ⊢Δ)
--       ([tF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ] (τCon _ _ _ _ ⊢Δ))
--       ([fF] {≤ε = ≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)} [ρ] (τCon _ _ _ _ ⊢Δ))
--       (≤-refl _) (goodCasesRefl _ _) (goodCasesRefl _ _)



--   --ϝᵣ-l [B] [A]t [A]f (GoodCases N {!!} [A]t [B] {!!} (goodCasesRefl _ _)) (GoodCases N {!!} [A]f [B] {!!} (goodCasesRefl _ _))




-- -- -- Construct an shape view from an equality (aptly named)
-- -- goodCases′ : ∀ {k k′ l} {lε : ⊢ₗ l} (N : Nat) ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
-- --             (A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ B / [A])
-- --             → (((μTy [B]) + (μConv A≡B)) ≤ N)
-- --             → ShapeView Γ k k′ A B [A] [B] A≡B
-- -- -- Diagonal cases
-- -- goodCases′ N (Uᵣ UA) (Uᵣ UB) (⊩¹≡U _ U≡B) N< = Uᵥ UA UB U≡B
-- -- goodCases′ N (ℕᵣ ℕA) (ℕᵣ ℕB) (⊩¹≡ℕ _ A⇒N) N< = ℕᵥ ℕA ℕB A⇒N
-- -- goodCases′ N (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (⊩¹≡𝔹 _ A⇒N) N< = 𝔹ᵥ 𝔹A 𝔹B A⇒N
-- -- goodCases′ N (ne neA) (ne neB) (⊩¹≡ne _ A=B) N< = ne neA neB A=B
-- -- goodCases′ N (Bᵣ BΣ ΣA) (Bᵣ BΣ ΣB) (⊩¹≡B BΣ _ A≡B) N< = Bᵥ BΣ ΣA ΣB A≡B
-- -- goodCases′ N (Bᵣ BΠ ΠA) (Bᵣ BΠ ΠB) (⊩¹≡B BΠ _ A≡B) N< = Bᵥ BΠ ΠA ΠB A≡B
-- -- -- goodCases′ N (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B N< = Emptyᵥ EmptyA EmptyB
-- -- -- goodCases′ N (Unitᵣ UnitA) (Unitᵣ UnitB) A≡B N< = Unitᵥ UnitA UnitB

-- -- goodCases′ {k = k} (1+ N) [A] (emb 0<1 x) A≡B (≤-s N<) =
-- --   emb¹⁰ (goodCases′ {k = k} {⁰} N [A] x A≡B N<)
-- -- goodCases′ {k′ = k} (1+ N) (emb 0<1 x) [B] (⊩¹≡emb _ [A] A≡B) N< =
-- --   emb⁰¹ (goodCases′ N [A] [B] A≡B (≤-pred (≤-trans (≤₊-s-swap (μTy [B]) (μConv A≡B)) N<)))


-- -- -- Left αNeutrals

-- -- goodCases′ (1+ N) [A] [B] (⊩¹≡ϝ _ tA fA tA≡B fA≡B) N<
-- --   with ≤-trans (≤₊-s-swap (μTy [B]) (max (μConv tA≡B) (μConv fA≡B))) N<
-- -- goodCases′ (1+ N) [A] [B] (⊩¹≡ϝ _ tA fA tA≡B fA≡B) N<
-- --   | ≤-s K< =
-- --  ϝᵣ-l [A] [B] tA fA (τTyLog [B]) (τTyLog [B]) tA≡B fA≡B
-- --     (goodCases′ N tA _ tA≡B
-- --       (≤-trans (≤-trans (≤₊-trans-l _ (τμTyLog [B]))
-- --                         (≤₊-trans-r _ (MaxLess-l (μConv tA≡B) (μConv fA≡B)))) K<))
-- --     (goodCases′ N fA _ fA≡B
-- --       (≤-trans (≤-trans (≤₊-trans-l _ (τμTyLog [B]))
-- --                         (≤₊-trans-r _ (MaxLess-r (μConv tA≡B) _))) K<))

-- -- --   with whrDet* (red A⇒B' , αₙ αB') (red A⇒B , αₙ αB)
-- -- -- goodCases′ N [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
-- -- --  | PE.refl with αNeutralHProp αB' αB
-- -- -- goodCases′ N [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
-- -- --  | PE.refl | PE.refl with NotInLConNatHProp _ _ mε' mε
-- -- -- goodCases′ N [A] (ϝᵣ mε A⇒B αB [A]t [A]f) (⊩¹≡ϝ-r {mε = mε'} A⇒B' αB' [A] tA fA tA≡B fA≡B)
-- -- --  | PE.refl | PE.refl | PE.refl =
-- -- --    ϝᵣ-r A⇒B A⇒B' αB αB' [A] tA fA [A]t [A]f tA≡B fA≡B
-- -- --         (goodCases′ N tA [A]t tA≡B) (goodCases′ N fA [A]f fA≡B)

-- -- -- Refutable cases
-- -- -- U ≡ _
-- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (ℕᵣ D) (⊩¹≡U _ PE.refl) with whnfRed* (red D) Uₙ
-- -- ... | ()
-- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (𝔹ᵣ D) (⊩¹≡U _ PE.refl) with whnfRed* (red D) Uₙ
-- -- ... | ()
-- -- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (Emptyᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- -- -- ... | ()
-- -- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (Unitᵣ D) PE.refl with whnfRed* (red D) Uₙ
-- -- -- ... | ()
-- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (ne′ K D neK K≡K) (⊩¹≡U _ PE.refl) N< =
-- --   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- -- goodCases′ N (Uᵣ′ _ _ ⊢Γ) (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡U _ PE.refl) N< =
-- --   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- -- goodCases′ (1+ N) (Uᵣ′ j j< ⊢Γ) (ϝᵣ mε [A]t [A]f) (⊩¹≡U _ PE.refl) (≤-s N<) =
-- --  ϝᵣ-r (Uᵣ′ _ _ ⊢Γ) (Uᵣ′ j j< (τCon _ _ _ _ ⊢Γ)) (Uᵣ′ j j< (τCon _ _ _ _ ⊢Γ))
-- --     [A]t [A]f (⊩¹≡U _ PE.refl) (⊩¹≡U _ PE.refl) (⊩¹≡U _ PE.refl)
-- --     (goodCases′ N _ [A]t (⊩¹≡U _ PE.refl) (≤-trans (≤₊-trans-l 0 (≤₊-l _ _)) N<))
-- --     (goodCases′ N _ [A]f (⊩¹≡U _ PE.refl) (≤-trans (≤₊-trans-l 0 (≤₊-r _ _)) N<))
     
-- -- -- -- Refutable right αNeutrals
-- -- -- goodCases′ N [A] (Uᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) N< =
-- -- --   ⊥-elim (U≢αne αB' (whnfRed* (red B⇒B') Uₙ))
-- -- -- goodCases′ N [A] (ℕᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) N< =
-- -- --   ⊥-elim (ℕ≢αne αB' (whrDet* (red D , ℕₙ) (red B⇒B' , αₙ αB')))
-- -- -- goodCases′ N [A] (𝔹ᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) N< =
-- -- --   ⊥-elim (𝔹≢αne αB' (whrDet* (red D , 𝔹ₙ) (red B⇒B' , αₙ αB')))
-- -- -- -- goodCases′ N [A] (Emptyᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) N< =
-- -- -- --   ⊥-elim (Empty≢αne αB' (whrDet* (red D , Emptyₙ) (red B⇒B' , αₙ αB')))
-- -- -- -- goodCases′ N [A] (Unitᵣ D) (⊩¹≡ϝ-r B⇒B' αB' [A] tA tB tA≡B fA≡B) N< =
-- -- -- --   ⊥-elim (Unit≢αne αB' (whrDet* (red D , Unitₙ) (red B⇒B' , αₙ αB')))
-- -- -- goodCases′ N [A] (ne′ K D neK K≡K) (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) N< =
-- -- --   ⊥-elim (ne≢αne neK αB' (whrDet* (red D , ne neK) (red B⇒B' , αₙ αB')))
-- -- -- goodCases′ N [A] (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --     (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) N< =
-- -- --     ⊥-elim (B≢αne BΠ αB' (whrDet* (red D , Πₙ) (red B⇒B' , αₙ αB')))
-- -- -- goodCases′ N [A] (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
-- -- --     (⊩¹≡ϝ-r B⇒B' αB' _ tA tB tA≡B fA≡B) N< =
-- -- --     ⊥-elim (B≢αne BΣ αB' (whrDet* (red D , Σₙ) (red B⇒B' , αₙ αB')))

-- -- -- ℕ ≡ _
-- -- goodCases′ {k = k} {k′ = k′} N (ℕᵣ D) (Uᵣ ⊢Γ) ℕ≡U N< =
-- --   ⊥-elim (ℕ≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ ℕ≡U)
-- -- goodCases′ N (ℕᵣ D) (𝔹ᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , 𝔹ₙ)
-- -- ... | ()
-- -- -- goodCases′ N (ℕᵣ D) (Emptyᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , Emptyₙ) (red D' , 𝔹ₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (ℕᵣ D) (Unitᵣ D') (⊩¹≡ℕ _ A⇒N) with whrDet* (A⇒N , ℕₙ) (red D' , Unitₙ)
-- -- -- ... | ()
-- -- goodCases′ N (ℕᵣ D) (ne′ K D₁ neK K≡K) (⊩¹≡ℕ _ A⇒N) N< =
-- --   ⊥-elim (ℕ≢ne neK (whrDet* (A⇒N , ℕₙ) (red D₁ , ne neK)))
-- -- goodCases′ N (ℕᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡ℕ _ A⇒N) N< =
-- --   ⊥-elim (ℕ≢B W (whrDet* (A⇒N , ℕₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- -- goodCases′ (1+ N) (ℕᵣ D) (ϝᵣ mε [A]t [A]f) (⊩¹≡ℕ _ A⇒N) (≤-s N<) =
-- --   ϝᵣ-r (ℕᵣ D) (ℕᵣ (τwfRed* D)) (ℕᵣ (τwfRed* D))
-- --      [A]t [A]f (⊩¹≡ℕ _ A⇒N) (⊩¹≡ℕ _ (τRed* A⇒N)) (⊩¹≡ℕ _ (τRed* A⇒N))
-- --      (goodCases′ N _ [A]t _ (≤-trans (≤₊-trans-l 0 (≤₊-l _ _)) N<))
-- --      (goodCases′ N _ [A]f _ (≤-trans (≤₊-trans-l 0 (≤₊-r _ _)) N<))


-- -- -- -- 𝔹 ≡ _
-- -- -- goodCases′ N (𝔹ᵣ 𝔹A) [B] A≡B N< = goodCases′ N𝔹 𝔹A [B] A≡B
-- -- goodCases′ {k = k} {k′ = k′} N (𝔹ᵣ D) (Uᵣ ⊢Γ) 𝔹≡U N< = ⊥-elim (𝔹≠U {_} {_} {_} {_} {_} {k} {k′} D ⊢Γ 𝔹≡U)
-- -- goodCases′ N (𝔹ᵣ D) (ℕᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , ℕₙ)
-- -- ... | ()
-- -- -- goodCases′ N (𝔹ᵣ D) (ℕᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , ℕₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (𝔹ᵣ D) (Unitᵣ D') (⊩¹≡𝔹 _ A⇒N) with whrDet* (A⇒N , 𝔹ₙ) (red D' , Unitₙ)
-- -- -- ... | ()
-- -- goodCases′ N (𝔹ᵣ D) (ne′ K D₁ neK K≡K) (⊩¹≡𝔹 _ A⇒N) N< =
-- --   ⊥-elim (𝔹≢ne neK (whrDet* (A⇒N , 𝔹ₙ) (red D₁ , ne neK)))
-- -- goodCases′ N (𝔹ᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡𝔹 _ A⇒N) N< =
-- --   ⊥-elim (𝔹≢B W (whrDet* (A⇒N , 𝔹ₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- -- goodCases′ (1+ N) (𝔹ᵣ D) (ϝᵣ mε [A]t [A]f) (⊩¹≡𝔹 _ A⇒N) (≤-s N<) =
-- --   ϝᵣ-r (𝔹ᵣ D) (𝔹ᵣ (τwfRed* D)) (𝔹ᵣ (τwfRed* D))
-- --      [A]t [A]f (⊩¹≡𝔹 _ A⇒N) (⊩¹≡𝔹 _ (τRed* A⇒N)) (⊩¹≡𝔹 _ (τRed* A⇒N))
-- --      (goodCases′ N _ [A]t _ (≤-trans (≤₊-trans-l 0 (≤₊-l _ _)) N<))
-- --      (goodCases′ N _ [A]f _ (≤-trans (≤₊-trans-l 0 (≤₊-r _ _)) N<))


-- -- -- -- Empty ≢ _
-- -- -- goodCases′ N (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B with whnfRed* A≡B Uₙ
-- -- -- ... | ()
-- -- -- goodCases′ N (Emptyᵣ _) (Unitᵣ D') D with whrDet* (red D' , Unitₙ) (D , Emptyₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (Emptyᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Emptyₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B N< =
-- -- --   ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
-- -- -- goodCases′ N (Emptyᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B N< =
-- -- --   ⊥-elim (Empty≢B W (whrDet* (A≡B , Emptyₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- -- -- goodCases′ N (Emptyᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B N< =
-- -- --  ⊥-elim (Empty≢αne αB (whrDet* (A≡B , Emptyₙ) (red A⇒B , αₙ αB)))


-- -- -- -- Unit ≡ _
-- -- -- goodCases′ N (Unitᵣ _) (Uᵣ x₁) A≡B with whnfRed* A≡B Uₙ
-- -- -- ... | ()
-- -- -- goodCases′ N (Unitᵣ _) (Emptyᵣ D') D with whrDet* (red D' , Emptyₙ) (D , Unitₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (Unitᵣ _) (ℕᵣ D') D with whrDet* (red D' , ℕₙ) (D , Unitₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (Unitᵣ D) (ne′ K D₁ neK K≡K) A≡B N< =
-- -- --   ⊥-elim (Unit≢ne neK (whrDet* (A≡B , Unitₙ) (red D₁ , ne neK)))
-- -- -- goodCases′ N (Unitᵣ D) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B N< =
-- -- --   ⊥-elim (Unit≢B W (whrDet* (A≡B , Unitₙ) (red D₁ , ⟦ W ⟧ₙ)))
-- -- -- goodCases′ N (Unitᵣ D) (ϝᵣ mε A⇒B αB [A]t [A]f) A≡B N< =
-- -- --   ⊥-elim (Unit≢αne αB (whrDet* (A≡B , Unitₙ) (red A⇒B , αₙ αB)))

-- -- -- ne ≡ _
-- -- -- goodCases′ N (ne neA) [B] A≡B N< = goodCases′ NNe neA [B] A≡B
-- -- goodCases′ N (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- --   ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
-- -- goodCases′ N (ne′ K D neK K≡K) (ℕᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- --   ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
-- -- goodCases′ N (ne′ K D neK K≡K) (𝔹ᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- --   ⊥-elim (𝔹≢ne neM (whrDet* (red D₁ , 𝔹ₙ) (red D′ , ne neM)))
-- -- -- goodCases′ N (ne′ K D neK K≡K) (Emptyᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- -- --   ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
-- -- -- goodCases′ N (ne′ K D neK K≡K) (Unitᵣ D₁) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- -- --  ⊥-elim (Unit≢ne neM (whrDet* (red D₁ , Unitₙ) (red D′ , ne neM)))
-- -- goodCases′ N (ne′ K D neK K≡K) (Bᵣ′ W F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) N< =
-- --   ⊥-elim (B≢ne W neM (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D′ , ne neM)))
-- -- goodCases′ (1+ N) (ne′ K D neK K≡K) (ϝᵣ mε [A]t [A]f)  (⊩¹≡ne _ (ne₌ M D′ neM K≡M)) (≤-s N<) =
-- --   ϝᵣ-r _ (ne′ K (τwfRed* D) neK (~-τ K≡K)) (ne′ K (τwfRed* D) neK (~-τ K≡K))
-- --     [A]t [A]f _ (⊩¹≡ne _ (ne₌ M (τwfRed* D′) neM (~-τ K≡M))) (⊩¹≡ne _ (ne₌ M (τwfRed* D′) neM (~-τ K≡M)))
-- --     (goodCases′ N _ [A]t _ (≤-trans (≤₊-trans-l 0 (≤₊-l _ _)) N<))
-- --     (goodCases′ N _ [A]f _ (≤-trans (≤₊-trans-l 0 (≤₊-r _ _)) N<))
-- --  -- ⊥-elim (ne≢αne neM αB (whrDet* (red D′ , ne neM) (red A⇒B , αₙ αB)))

-- -- -- Π ≡ _
-- -- -- goodCases′ N (Bᵣ W BA) ⊢B A≡B N< = goodCases′ NW W BA ⊢B A≡B


-- -- goodCases′ N (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
-- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whnfRed* D′ Uₙ
-- -- ... | ()
-- -- goodCases′ N (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
-- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whnfRed* D′ Uₙ
-- -- ... | ()
-- -- goodCases′ N (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
-- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) N< =
-- --           ⊥-elim (ℕ≢B W (whrDet* (red D₁ , ℕₙ) (D′ , ⟦ W ⟧ₙ)))
-- -- goodCases′ N (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (𝔹ᵣ D₁)
-- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) N< =
-- --           ⊥-elim (𝔹≢B W (whrDet* (red D₁ , 𝔹ₙ) (D′ , ⟦ W ⟧ₙ)))
-- -- -- goodCases′ N (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
-- -- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whrDet* (red D₁ , Emptyₙ) (D′ , Σₙ)
-- -- -- ... | ()
-- -- -- goodCases′ N (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ D₁)
-- -- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) with whrDet* (red D₁ , Unitₙ) (D′ , Σₙ)
-- -- -- ... | ()
-- -- goodCases′ N (Bᵣ′ BΣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΠ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
-- --   (⊩¹≡B _ _ (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′])) with whrDet* (red D′ , Πₙ) (D′₁ , Σₙ)
-- -- ... | ()
-- -- goodCases′ N (Bᵣ′ BΠ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ′ BΣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)
-- --   (⊩¹≡B _ _ (B₌ F′₁ G′₁ D′₁ A≡B [F≡F′] [G≡G′])) with whrDet* (red D′ , Σₙ) (D′₁ , Πₙ)
-- -- ... | ()
-- -- goodCases′ N (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
-- --           (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) N< =
-- --   ⊥-elim (B≢ne W neK (whrDet* (D′ ,  ⟦ W ⟧ₙ) (red D₁ , ne neK)))
-- -- goodCases′ (1+ N) [A]@(Bᵣ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ϝᵣ mε [A]t [A]f) 
-- --             (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])) (≤-s N<) =
-- --            ϝᵣ-r [A]
-- --               (Bᵣ′ W F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A)
-- --                 (λ {m = m₁} {l'} {≤ε} → [F] {≤ε = λ n b nε → ≤ε n b (InThere _ nε _ _)}) [G] G-ext)
-- --               (Bᵣ′ W F G (τwfRed* D) (τTy _ _ _ _ ⊢F) (τTy _ _ _ _ ⊢G) (≅-τ A≡A)
-- --                 (λ {m = m₁} {l'} {≤ε} → [F] {≤ε = λ n b nε → ≤ε n b (InThere _ nε _ _)}) [G] G-ext)
-- --               [A]t [A]f  (⊩¹≡B _ _ (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]))
-- --               (⊩¹≡B _ _ (B₌ F′ G′ (τRed* D′) (≅-τ A≡B)
-- --                 (λ {m = m₁} {ρ} {Δ} {l'} {≤ε} → [F≡F′] {≤ε = λ n b nε → ≤ε n b (InThere _ nε _ _)})
-- --                 [G≡G′]))
-- --               (⊩¹≡B _ _ (B₌ F′ G′ (τRed* D′) (≅-τ A≡B)
-- --                 (λ {m = m₁} {ρ} {Δ} {l'} {≤ε} → [F≡F′] {≤ε = λ n b nε → ≤ε n b (InThere _ nε _ _)})
-- --                 [G≡G′]))
-- --               (goodCases′ N _ [A]t _ (≤-trans (≤₊-trans-l 0 (≤₊-l _ _)) N<))
-- --               (goodCases′ N _ [A]f _ (≤-trans (≤₊-trans-l 0 (≤₊-r _ _)) N<))

-- -- goodCases : ∀ {k k′ l} {lε : ⊢ₗ l} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([B] : Γ / lε ⊩⟨ k′ ⟩ B)
-- --             (A≡B : Γ / lε ⊩⟨ k ⟩ A ≡ B / [A])
-- --             → ShapeView Γ k k′ A B [A] [B] A≡B
-- -- goodCases [A] [B] A≡B = goodCases′ _ [A] [B] A≡B (≤-refl _)

-- -- -- Construct an shape view between two derivations of the same type
-- -- goodCasesRefl : ∀ {k k′ l} {lε : ⊢ₗ l} ([A] : Γ / lε ⊩⟨ k ⟩ A) ([A′] : Γ / lε ⊩⟨ k′ ⟩ A)
-- --               → ShapeView Γ k k′ A A [A] [A′] (reflEq [A])
-- -- goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])





-- -- -- -- A view for constructor equality between three types
-- -- -- data ShapeView₃ (Γ : Con Term n) : ∀ {l : LCon} {lε : ⊢ₗ l} k k′ k″ A B C
-- -- --                  (p : Γ / lε ⊩⟨ k   ⟩ A)
-- -- --                  (q : Γ / lε ⊩⟨ k′  ⟩ B)
-- -- --                  (r : Γ / lε ⊩⟨ k″ ⟩ C)
-- -- --                  (A≡B :  Γ / lε ⊩⟨ k ⟩ A ≡ B / p)
-- -- --                  (B≡C :  Γ / lε ⊩⟨ k′ ⟩ B ≡ C / q) → Set where
-- -- --   Uᵥ : ∀ {l lε k k′ k″} UA UB UC U≡B U≡C
-- -- --      → ShapeView₃ Γ {l} {lε} k k′ k″ U U U (Uᵣ UA) (Uᵣ UB) (Uᵣ UC) (⊩¹≡U UA U≡B) (⊩¹≡U UB U≡C)
-- -- --   ℕᵥ : ∀ {A B C k k′ k″} ℕA ℕB ℕC ℕ≡B ℕ≡C
-- -- --     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC) (⊩¹≡ℕ ℕA ℕ≡B) (⊩¹≡ℕ ℕB ℕ≡C)
-- -- --   𝔹ᵥ : ∀ {A B C k k′ k″} 𝔹A 𝔹B 𝔹C 𝔹≡B 𝔹≡C
-- -- --     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (𝔹ᵣ 𝔹C) (⊩¹≡𝔹 𝔹A 𝔹≡B) (⊩¹≡𝔹 𝔹B 𝔹≡C)
-- -- -- --   Emptyᵥ : ∀ {l} {lε}  {A B C k k′ k″} EmptyA EmptyB EmptyC
-- -- -- --     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
-- -- -- --   Unitᵥ : ∀ {l} {lε}  {A B C k k′ k″} UnitA UnitB UnitC
-- -- -- --     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ UnitC)
-- -- --   ne  : ∀ {l} {lε}  {A B C k k′ k″} neA neB neC neA≡B neB≡C
-- -- --       → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (ne neA) (ne neB) (ne neC) (⊩¹≡ne neA neA≡B) (⊩¹≡ne neB neB≡C)
-- -- --   Bᵥ : ∀ {l} {lε}  {A B C k k′ k″} W BA BB BC BA≡B BB≡C
-- -- --     → ShapeView₃ Γ {l} {lε}  k k′ k″ A B C (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W BC) (⊩¹≡B W BA BA≡B) (⊩¹≡B W BB BB≡C)

-- -- --   ϝᵣ : ∀ {l lε n nε} {k k' k'' A B C} [A] [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f
-- -- --            A≡B B≡C tA≡B fA≡B tB≡C fB≡C 
-- -- --          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C [A]t [B]t [C]t tA≡B tB≡C
-- -- --          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C [A]f [B]f [C]f fA≡B fB≡C
-- -- --          → ShapeView₃ Γ {l} {lε}                  k k' k'' A  B C [A] [B] [C] A≡B B≡C
  
-- -- -- --   ϝᵣ-l : ∀ {l lε n nε} {k k' k'' A A' B C} (A⇒A' : Γ / lε ⊢ A :⇒*: A') αA [B] [C] [A]t [A]f [B]t [B]f [C]t [C]f
-- -- -- --            B≡C tA≡B fA≡B tB≡C fB≡C 
-- -- -- --          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Btrue nε}  k k' k'' A B C [A]t [B]t [C]t tA≡B tB≡C
-- -- -- --          → ShapeView₃ Γ {_} {⊢ₗ• l lε n Bfalse nε} k k' k'' A B C [A]f [B]f [C]f fA≡B fB≡C
-- -- -- --          → ShapeView₃ Γ {l} {lε}                  k k' k'' A  B C (ϝᵣ nε A⇒A' αA [A]t [A]f) [B] [C]
-- -- -- --                                                                       (⊩¹≡ϝ-l A⇒A' αA [A]t [A]f tA≡B fA≡B) B≡C
-- -- --   emb⁰¹¹ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
-- -- --          → ShapeView₃ Γ {l} {lε}  ⁰ k k′ A B C p q r A≡B B≡C
-- -- --          → ShapeView₃ Γ {l} {lε}  ¹ k k′ A B C (emb 0<1 p) q r (⊩¹≡emb 0<1 p A≡B) B≡C
-- -- --   emb¹⁰¹ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
-- -- --          → ShapeView₃ Γ {l} {lε}  k ⁰ k′ A B C p q r A≡B B≡C
-- -- --          → ShapeView₃ Γ {l} {lε}  k ¹ k′ A B C p (emb 0<1 q) r A≡B (⊩¹≡emb 0<1 q B≡C)
-- -- --   emb¹¹⁰ : ∀ {l} {lε}  {A B C k k′ p q r A≡B B≡C}
-- -- --          → ShapeView₃ Γ {l} {lε}  k k′ ⁰ A B C p q r A≡B B≡C
-- -- --          → ShapeView₃ Γ {l} {lε}  k k′ ¹ A B C p q (emb 0<1 r) A≡B B≡C


-- -- -- -- combineW-l : ∀ W {W'} {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C BA BB [B]′ [C]}
-- -- -- --   → ShapeView Γ {l} {lε} k k′ A B (Bᵣ W BA) (Bᵣ W' BB)
-- -- -- --   → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- --   → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Bᵣ W BA) (Bᵣ W' BB) [C]
-- -- -- -- combineW-l BΠ (Bᵥ BΠ ΠA₁ ΠB₁) (Bᵥ BΠ ΠA ΠB) = Bᵥ BΠ ΠA₁ ΠB₁ ΠB
-- -- -- -- combineW-l BΣ (Bᵥ BΣ ΣA₁ ΣB₁) (Bᵥ BΣ ΣA ΣB) = Bᵥ BΣ ΣA₁ ΣB₁ ΣB
-- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ϝᵣ [A] [B] [A]t [A]f [B]t [B]f A≡B tA≡B fA≡B tAB fAB) =
-- -- -- --   ?
-- -- -- -- -- combineW-l W (Bᵥ W BA BB) (ϝᵣ-r B⇒B' αB [A] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- --   ϝᵣ-r B⇒B' αB (Bᵣ W BA) (Bᵣ W BB) (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA)) (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA))
-- -- -- -- --     (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB))
-- -- -- -- --     (Bᵣ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) [B]t [B]f
-- -- -- -- --       (combineW-l W (Bᵥ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) tAB)
-- -- -- -- --       (combineW-l W (Bᵥ W (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BA) (LogRel.τ⊩¹B _ (logRelRec _) _ _ _ W _ BB)) fAB)
-- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
-- -- -- --   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
-- -- -- --   ⊥-elim (ℕ≢B W (whrDet* (red ℕA , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (𝔹ᵥ 𝔹A 𝔹B) =
-- -- -- --   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹A , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
-- -- -- -- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyA , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Unitᵥ UnitA UnitB) =
-- -- -- -- --   ⊥-elim (Unit≢B W (whrDet* (red UnitA , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- combineW-l W (Bᵥ W BA (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
-- -- -- --   ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
-- -- -- -- combineW-l W (Bᵥ BΠ ΠA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΣA)
-- -- -- --   with whrDet* (red D , Πₙ) (red D′ , Σₙ)
-- -- -- -- ... | ()
-- -- -- -- combineW-l W (Bᵥ BΣ ΣA (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Bᵥ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′) ΠA)
-- -- -- --   with whrDet* (red D , Σₙ) (red D′ , Πₙ)
-- -- -- -- ... | ()
-- -- -- --         --  combineW-l W (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combineW-l W [AB] [BC])
-- -- -- -- combineW-l W [AB] (emb⁰¹ [BC]) = (combineW-l W [AB] [BC])
-- -- -- -- combineW-l W [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineW-l W [AB] [BC])


-- -- -- -- -- combineU : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ UA UB C [B]′ [C]}
-- -- -- -- --           → ShapeView Γ {l} {lε} k k′ U U (Uᵣ UA) (Uᵣ UB)
-- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ U C [B]′ [C]
-- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ U U C (Uᵣ UA) (Uᵣ UB) [C]
-- -- -- -- -- combineU (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
-- -- -- -- -- combineU [AB] (emb⁰¹ [BC]) = combineU [AB] [BC]
-- -- -- -- -- combineU [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineU [AB] [BC])
-- -- -- -- -- combineU (Uᵥ UA UB) (ℕᵥ ℕA ℕB) with whnfRed* (red ℕA) Uₙ
-- -- -- -- -- ... | ()
-- -- -- -- -- combineU (Uᵥ UA UB) (𝔹ᵥ 𝔹A 𝔹B) with whnfRed* (red 𝔹A) Uₙ
-- -- -- -- -- ... | ()
-- -- -- -- -- -- combineU (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) with whnfRed* (red EmptyA) Uₙ
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineU (Uᵥ UA UB) (Unitᵥ UnA UnB) with whnfRed* (red UnA) Uₙ
-- -- -- -- -- -- ... | ()
-- -- -- -- -- combineU (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
-- -- -- -- --   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- -- -- -- -- combineU (Uᵥ UA UB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- --   ⊥-elim (U≢B W (whnfRed* (red D) Uₙ))
-- -- -- -- -- combineU (Uᵥ UA UB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- --   ⊥-elim (U≢αne αA (whnfRed* (red A⇒A') Uₙ))
-- -- -- -- -- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC)
-- -- -- -- --   with TyLogU [B]t
-- -- -- -- -- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) | (tUC , PE.refl)
-- -- -- -- --   with TyLogU [B]f
-- -- -- -- -- combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ) (Uᵣ _ 0<1 ⊢Γ')) (ϝᵣ-r C⇒C' αC [B] (Uᵣ tUC) [B]f [C]t [C]f tBC fBC)
-- -- -- -- --   | ((Uᵣ _ 0<1 ⊢Γ'') , PE.refl) | ((Uᵣ _ 0<1 ⊢Γ''') , PE.refl) =
-- -- -- -- --     ϝᵣ-r C⇒C' αC (Uᵣ (Uᵣ _ 0<1 ⊢Γ)) (Uᵣ (Uᵣ _ 0<1 ⊢Γ'))
-- -- -- -- --       (Uᵣ (Uᵣ _ 0<1 ⊢Γ'')) (Uᵣ (Uᵣ _ 0<1 ⊢Γ'''))
-- -- -- -- --       (Uᵣ (Uᵣ _ 0<1 ⊢Γ'')) (Uᵣ (Uᵣ _ 0<1 ⊢Γ''')) [C]t [C]f
-- -- -- -- --       (combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ'') (Uᵣ _ 0<1 ⊢Γ'')) tBC)
-- -- -- -- --       (combineU (Uᵥ (Uᵣ _ 0<1 ⊢Γ''') (Uᵣ _ 0<1 ⊢Γ''')) fBC)

-- -- -- -- -- combineℕ : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C ℕA ℕB [B]′ [C]}
-- -- -- -- --           → ShapeView Γ {l} {lε} k k′ A B (ℕᵣ ℕA) (ℕᵣ ℕB)
-- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (ℕᵣ ℕA) (ℕᵣ ℕB) [C]
-- -- -- -- -- combineℕ (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
-- -- -- -- -- combineℕ [AB] (emb⁰¹ [BC]) = combineℕ [AB] [BC]
-- -- -- -- -- combineℕ [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineℕ [AB] [BC])
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (Uᵥ UA UB) with whnfRed* (red ℕB) Uₙ
-- -- -- -- -- ... | ()
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (𝔹ᵥ 𝔹A 𝔹B) with whrDet* (red ℕB , ℕₙ) (red 𝔹A , 𝔹ₙ)
-- -- -- -- -- ... | ()
-- -- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (Unitᵥ UnA UnB) with whrDet* (red ℕB , ℕₙ) (red UnA , Unitₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
-- -- -- -- --   ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- --   ⊥-elim (ℕ≢B W (whrDet* (red ℕB , ℕₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- --   ⊥-elim (ℕ≢αne αA (whrDet* (red ℕB , ℕₙ) (red A⇒A' , αₙ αA)))
-- -- -- -- -- combineℕ (ℕᵥ ℕA ℕB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- -- -- -- --   ϝᵣ-r C⇒C' αC (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ (τwfRed* ℕA)) (ℕᵣ (τwfRed* ℕA))
-- -- -- -- --     (ℕᵣ (τwfRed* ℕB)) (ℕᵣ (τwfRed* ℕB)) [C]t [C]f
-- -- -- -- --     (combineℕ (ℕᵥ (τwfRed* ℕA) (τwfRed* ℕB)) tBC)
-- -- -- -- --     (combineℕ (ℕᵥ (τwfRed* ℕA) (τwfRed* ℕB)) fBC)

-- -- -- -- -- combine𝔹 : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C 𝔹A 𝔹B [B]′ [C]}
-- -- -- -- --           → ShapeView Γ {l} {lε} k k′ A B (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B)
-- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) [C]
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A₁ 𝔹B₁) (𝔹ᵥ 𝔹A 𝔹B) = 𝔹ᵥ 𝔹A₁ 𝔹B₁ 𝔹B
-- -- -- -- -- combine𝔹 [AB] (emb⁰¹ [BC]) = combine𝔹 [AB] [BC]
-- -- -- -- -- combine𝔹 [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine𝔹 [AB] [BC])
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Uᵥ UA UB) with whnfRed* (red 𝔹B) Uₙ
-- -- -- -- -- ... | ()
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ℕᵥ ℕA ℕB) with whrDet* (red 𝔹B , 𝔹ₙ) (red ℕA , ℕₙ)
-- -- -- -- -- ... | ()
-- -- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Emptyᵥ EmptyA EmptyB) with whrDet* (red 𝔹B , 𝔹ₙ) (red EmptyA , Emptyₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Unitᵥ UnA UnB) with whrDet* (red 𝔹B , 𝔹ₙ) (red UnA , Unitₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ne (ne K D neK K≡K) neB) =
-- -- -- -- --   ⊥-elim (𝔹≢ne neK (whrDet* (red 𝔹B , 𝔹ₙ) (red D , ne neK)))
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- --   ⊥-elim (𝔹≢B W (whrDet* (red 𝔹B , 𝔹ₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- --   ⊥-elim (𝔹≢αne αA (whrDet* (red 𝔹B , 𝔹ₙ) (red A⇒A' , αₙ αA)))
-- -- -- -- -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- -- -- -- --   ϝᵣ-r C⇒C' αC (𝔹ᵣ 𝔹A) (𝔹ᵣ 𝔹B) (𝔹ᵣ (τwfRed* 𝔹A)) (𝔹ᵣ (τwfRed* 𝔹A))
-- -- -- -- --     (𝔹ᵣ (τwfRed* 𝔹B)) (𝔹ᵣ (τwfRed* 𝔹B)) [C]t [C]f
-- -- -- -- --     (combine𝔹 (𝔹ᵥ (τwfRed* 𝔹A) (τwfRed* 𝔹B)) tBC)
-- -- -- -- --     (combine𝔹 (𝔹ᵥ (τwfRed* 𝔹A) (τwfRed* 𝔹B)) fBC)


-- -- -- -- -- -- combineUnit : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C UnitA UnitB [B]′ [C]}
-- -- -- -- -- --           → ShapeView Γ {l} {lε} k k′ A B (Unitᵣ UnitA) (Unitᵣ UnitB)
-- -- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Unitᵣ UnitA) (Unitᵣ UnitB) [C]
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA₁ UnitB₁) (Unitᵥ UnitA UnitB) = Unitᵥ UnitA₁ UnitB₁ UnitB
-- -- -- -- -- -- combineUnit [AB] (emb⁰¹ [BC]) = combineUnit [AB] [BC]
-- -- -- -- -- -- combineUnit [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineUnit [AB] [BC])
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (Uᵥ UA UB) with whnfRed* (red UnitB) Uₙ
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (ℕᵥ ℕA ℕB) with whrDet* (red UnitB , Unitₙ) (red ℕA , ℕₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (Emptyᵥ EmptyA EmptyB) with whrDet* (red UnitB , Unitₙ) (red EmptyA , Emptyₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (ne (ne K D neK K≡K) neB) =
-- -- -- -- -- --   ⊥-elim (Unit≢ne neK (whrDet* (red UnitB , Unitₙ) (red D , ne neK)))
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- -- --   ⊥-elim (Unit≢B W (whrDet* (red UnitB , Unitₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- -- --   ⊥-elim (Unit≢αne αA (whrDet* (red UnitB , Unitₙ) (red A⇒A' , αₙ αA)))
-- -- -- -- -- -- combineUnit (Unitᵥ UnitA UnitB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- -- -- -- -- --   ϝᵣ-r C⇒C' αC (Unitᵣ UnitA) (Unitᵣ UnitB) (Unitᵣ (τwfRed* UnitA)) (Unitᵣ (τwfRed* UnitA))
-- -- -- -- -- --     (Unitᵣ (τwfRed* UnitB)) (Unitᵣ (τwfRed* UnitB)) [C]t [C]f
-- -- -- -- -- --     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) tBC)
-- -- -- -- -- --     (combineUnit (Unitᵥ (τwfRed* UnitA) (τwfRed* UnitB)) fBC)


-- -- -- -- -- -- combineE : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C EA EB [B]′ [C]}
-- -- -- -- -- --           → ShapeView Γ {l} {lε} k k′ A B (Emptyᵣ EA) (Emptyᵣ EB)
-- -- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (Emptyᵣ EA) (Emptyᵣ EB) [C]
-- -- -- -- -- -- combineE (Emptyᵥ EA₁ EB₁) (Emptyᵥ EA EB) = Emptyᵥ EA₁ EB₁ EB
-- -- -- -- -- -- combineE [AB] (emb⁰¹ [BC]) = combineE [AB] [BC]
-- -- -- -- -- -- combineE [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineE [AB] [BC])
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) with whnfRed* (red EmptyB) Uₙ
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) with whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (Unitᵥ UnA UnB) with whrDet* (red EmptyB , Emptyₙ) (red UnA , Unitₙ)
-- -- -- -- -- -- ... | ()
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
-- -- -- -- -- --   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (Bᵥ W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- -- --   ⊥-elim (Empty≢B W (whrDet* (red EmptyB , Emptyₙ) (red D , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- combineE (Emptyᵥ EmptyA EmptyB) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- -- --   ⊥-elim (Empty≢αne αA (whrDet* (red EmptyB , Emptyₙ) (red A⇒A' , αₙ αA)))
-- -- -- -- -- -- combineE (Emptyᵥ EA EB) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) =
-- -- -- -- -- --   ϝᵣ-r C⇒C' αC (Emptyᵣ EA) (Emptyᵣ EB) (Emptyᵣ (τwfRed* EA)) (Emptyᵣ (τwfRed* EA))
-- -- -- -- -- --     (Emptyᵣ (τwfRed* EB)) (Emptyᵣ (τwfRed* EB)) [C]t [C]f
-- -- -- -- -- --     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) tBC)
-- -- -- -- -- --     (combineE (Emptyᵥ (τwfRed* EA) (τwfRed* EB)) fBC)


-- -- -- -- -- combineNe : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C neA neB [B]′ [C]}
-- -- -- -- --           → ShapeView Γ {l} {lε} k k′ A B (ne neA) (ne neB)
-- -- -- -- --           → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C]
-- -- -- -- --           → ShapeView₃ Γ {l} {lε} k k′ k‴ A B C (ne neA) (ne neB) [C]
-- -- -- -- -- combineNe (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
-- -- -- -- -- combineNe [AB] (emb⁰¹ [BC]) = combineNe [AB] [BC]
-- -- -- -- -- combineNe [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combineNe [AB] [BC])
-- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
-- -- -- -- --   ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
-- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
-- -- -- -- --   ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
-- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (𝔹ᵥ 𝔹A 𝔹B) =
-- -- -- -- --   ⊥-elim (𝔹≢ne neK (whrDet* (red 𝔹A , 𝔹ₙ) (red D , ne neK)))
-- -- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
-- -- -- -- -- --   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
-- -- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (Unitᵥ UnA UnB) =
-- -- -- -- -- --   ⊥-elim (Unit≢ne neK (whrDet* (red UnA , Unitₙ) (red D , ne neK)))
-- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (Bᵥ W (Bᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) BB) =
-- -- -- -- --   ⊥-elim (B≢ne W neK (whrDet* (red D₁ , ⟦ W ⟧ₙ) (red D , ne neK)))
-- -- -- -- -- combineNe (ne neA (ne K D neK K≡K)) (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) =
-- -- -- -- --   ⊥-elim (ne≢αne neK αA (whrDet* (red D , ne neK) (red A⇒A' , αₙ αA)))
-- -- -- -- -- combineNe (ne (ne K D neK K≡K) (ne K' D' neK' K≡K')) (ϝᵣ-r C⇒C' αC [B] [B]t [B]f [C]t [C]f tBC fBC) = 
-- -- -- -- --   ϝᵣ-r C⇒C' αC (ne (ne K D neK K≡K)) (ne (ne K' D' neK' K≡K'))
-- -- -- -- --     (ne (ne K (τwfRed* D) neK (~-τ K≡K))) (ne (ne K (τwfRed* D) neK (~-τ K≡K)))
-- -- -- -- --     (ne (ne K' (τwfRed* D') neK' (~-τ K≡K'))) (ne (ne K' (τwfRed* D') neK' (~-τ K≡K'))) [C]t [C]f
-- -- -- -- --     (combineNe (ne (ne K (τwfRed* D) neK (~-τ K≡K)) (ne K' (τwfRed* D') neK' (~-τ K≡K'))) tBC)
-- -- -- -- --     (combineNe (ne (ne K (τwfRed* D) neK (~-τ K≡K)) (ne K' (τwfRed* D') neK' (~-τ K≡K'))) fBC)


  
-- -- -- -- --   Combines two two-way views into a three-way view

-- -- -- -- -- combine : ∀ {l : LCon} {lε : ⊢ₗ l} {k k′ k″ k‴ A B C [A] [B] [B]′ [C] A≡B B≡C}
-- -- -- -- --         → ShapeView Γ {l} {lε} k k′ A B [A] [B] A≡B 
-- -- -- -- --         → ShapeView Γ {l} {lε} k″ k‴ B C [B]′ [C] B≡C
-- -- -- -- --         → ShapeView₃ Γ {l} {lε} k k″ k‴ A B C [A] [B]′ [C] A≡B B≡C
-- -- -- -- -- -- Diagonal cases
-- -- -- -- -- combine (emb⁰¹ [AB]) [BC] = {!!} -- emb⁰¹¹ (combine [AB] [BC])
-- -- -- -- -- combine (emb¹⁰ [AB]) [BC] = {!!} -- emb¹⁰¹ (combine [AB] [BC])
-- -- -- -- -- combine [AB] (emb⁰¹ [BC]) = {!!} -- combine [AB] [BC]
-- -- -- -- -- combine [AB] (emb¹⁰ [BC]) = {!!} -- emb¹¹⁰ (combine [AB] [BC])
                                                 
-- -- -- -- -- -- Π/Σ ≡ _
-- -- -- -- -- combine (Bᵥ W BA BB BA≡B) [BC] = {!!} --combineW-l W (Bᵥ W BA BB) [BC]

                                                      
-- -- -- -- -- -- U ≡ _
-- -- -- -- -- combine (Uᵥ UA UB UA≡B) [BC] = {!!} -- combineU (Uᵥ UA UB) [BC]

-- -- -- -- -- -- ℕ ≡ _
-- -- -- -- -- combine (ℕᵥ ℕA ℕB ℕA≡B) [BC] = {!!} -- combineℕ (ℕᵥ ℕA ℕB) [BC]

-- -- -- -- -- -- 𝔹 ≡ _
-- -- -- -- -- combine (𝔹ᵥ 𝔹A 𝔹B 𝔹A≡B) [BC] = {!!} -- combine𝔹 (𝔹ᵥ 𝔹A 𝔹B) [BC]

-- -- -- -- -- -- -- Empty ≡ _
-- -- -- -- -- -- combine (Emptyᵥ EmptyA EmptyB) = combineE (Emptyᵥ EmptyA EmptyB) 

-- -- -- -- -- -- -- Unit ≡ _
-- -- -- -- -- -- combine (Unitᵥ UnitA UnitB) = combineUnit (Unitᵥ UnitA UnitB)

-- -- -- -- -- -- ne ≡ _
-- -- -- -- -- combine (ne neA neB neA≡B) = {!!} -- combineNe (ne neA neB)
                                         
-- -- -- -- -- -- combine (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB) (ne neB (ne K D neK K≡K)) = {!!}
-- -- -- -- -- combine {[C] = [C]} (ϝᵣ-l A⇒A' αA [B] [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) [BC] = {!!}
-- -- -- -- -- --  ϝᵣ-l A⇒A' αA [B] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
-- -- -- -- -- --       (combine tAB (ShapeView≤ [BC] [B]t (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
-- -- -- -- -- --       (combine fAB (ShapeView≤ [BC] [B]f (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
                                                                                 
-- -- -- -- -- combine {[B]′ = [B]′} {[C] = [C]} (ϝᵣ-r B⇒B' B⇒B'' αB αB' [A] [A]t [A]f [B]t [B]f tAB fAB tA≡B fA≡B) [BC] = {!!}
-- -- -- -- -- --  ϝᵣ-m B⇒B' αB [A] [C] [A]t [A]f [B]t [B]f (τTyLog [C]) (τTyLog [C])
-- -- -- -- -- --  (combine tAB (ShapeView≤ [BC] (τTyLog [B]′) (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
-- -- -- -- -- --  (combine fAB (ShapeView≤ [BC] (τTyLog [B]′) (τTyLog [C]) (λ n₁ b e → InThere _ e _ _)))
                                                                                


-- -- -- -- -- -- TyLogℕ : ∀ {l : LCon} {lε : ⊢ₗ l} {k}
-- -- -- -- -- --            → (ℕA : Γ / lε ⊩ℕ A)
-- -- -- -- -- --            → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
-- -- -- -- -- --            → ∃ (λ K → [A] PE.≡ ℕ-intr K) -- TS.⊎ ∃₂ (λ k' (k< : k' < k) → ∃ (λ K → [A] PE.≡ emb k< (ℕᵣ K)))
-- -- -- -- -- -- TyLogℕ {k = k} ℕA [A] with goodCasesRefl {k = k} (ℕᵣ ℕA) [A]
-- -- -- -- -- -- TyLogℕ ℕA [A] | ℕᵥ ℕA ℕA' = noemb ℕA' , PE.refl
-- -- -- -- -- -- TyLogℕ ℕA (emb 0<1 [A]) | emb¹⁰ [AB] with TyLogℕ ℕA [A]
-- -- -- -- -- -- TyLogℕ ℕA (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- -- -- -- -- TyLogℕ ℕA [A] | ϝᵣ-r B⇒B' αB (ℕᵣ ℕA) [A]t [A]f [B]t [B]f tAB fAB = ⊥-elim (ℕ≢αne αB (whrDet* (red ℕA , ℕₙ) (red B⇒B' , αₙ αB)))

-- -- -- -- -- -- TyLog𝔹 : ∀ {l : LCon} {lε : ⊢ₗ l} {k}
-- -- -- -- -- --            → (𝔹A : Γ / lε ⊩𝔹 A)
-- -- -- -- -- --            → ([A] :  Γ / lε ⊩⟨ k ⟩ A)
-- -- -- -- -- --            → ∃ (λ K → [A] PE.≡ 𝔹-intr K) -- TS.⊎ ∃₂ (λ k' (k< : k' < k) → ∃ (λ K → [A] PE.≡ emb k< (𝔹ᵣ K)))
-- -- -- -- -- -- TyLog𝔹 {k = k} 𝔹A [A] with goodCasesRefl {k = k} (𝔹ᵣ 𝔹A) [A]
-- -- -- -- -- -- TyLog𝔹 𝔹A [A] | 𝔹ᵥ 𝔹A 𝔹A' = noemb 𝔹A' , PE.refl
-- -- -- -- -- -- TyLog𝔹 𝔹A (emb 0<1 [A]) | emb¹⁰ [AB] with TyLog𝔹 𝔹A [A]
-- -- -- -- -- -- TyLog𝔹 𝔹A (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- -- -- -- -- TyLog𝔹 𝔹A [A] | ϝᵣ-r B⇒B' αB (𝔹ᵣ 𝔹A) [A]t [A]f [B]t [B]f tAB fAB = ⊥-elim (𝔹≢αne αB (whrDet* (red 𝔹A , 𝔹ₙ) (red B⇒B' , αₙ αB)))


-- -- -- -- -- -- TyLogW : ∀ {l : LCon} {lε : ⊢ₗ l} {k k'} W
-- -- -- -- -- --            → (WA : Γ / lε ⊩′⟨ k ⟩B⟨ W ⟩ A)
-- -- -- -- -- --            → ([A] :  Γ / lε ⊩⟨ k' ⟩ A)
-- -- -- -- -- --            → ∃ (λ K → [A] PE.≡ B-intr W K)
-- -- -- -- -- -- TyLogW {k = k} W WA [A] with goodCasesRefl {k = k} (Bᵣ W WA) [A]
-- -- -- -- -- -- TyLogW W WA [A] | Bᵥ W BA BA' = noemb BA' , PE.refl
-- -- -- -- -- -- TyLogW W WA (emb 0<1 [A]) | emb¹⁰ [AB] with TyLogW W WA [A]
-- -- -- -- -- -- TyLogW W WA (emb 0<1 [A]) | emb¹⁰ [AB] | K , PE.refl = emb 0<1 K , PE.refl
-- -- -- -- -- -- TyLogW W WA [A] | ϝᵣ-r B⇒B' αB (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) [A]t [A]f [B]t [B]f tAB fAB =
-- -- -- -- -- --   ⊥-elim (B≢αne W αB (whrDet* (red D , ⟦ W ⟧ₙ) (red B⇒B' , αₙ αB)))



-- -- -- -- -- -- -- LogW0 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
-- -- -- -- -- -- --        ([A] : Γ / lε' ⊩⟨ ⁰ ⟩ A) (f< : l ≤ₗ l')
-- -- -- -- -- -- --        → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA'))
-- -- -- -- -- -- -- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = (BA' , PE.refl)
-- -- -- -- -- -- -- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = (BA' , PE.refl)
-- -- -- -- -- -- -- LogW0 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- -- -- -- -- --   with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
-- -- -- -- -- -- -- ... | ()
-- -- -- -- -- -- -- LogW0 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- -- -- -- -- --   with (whrDet* ( red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
-- -- -- -- -- -- -- ... | ()
-- -- -- -- -- -- -- LogW0 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
-- -- -- -- -- -- --   ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (emb () [A]) 
-- -- -- -- -- -- -- LogW0 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
-- -- -- -- -- -- --   ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))


-- -- -- -- -- -- -- LogW1 : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {k A} W (BA : (k LogRel./ logRelRec k ⊩¹B⟨ Γ ⟩ lε) W A)
-- -- -- -- -- -- --        ([A] : Γ / lε' ⊩⟨ ¹ ⟩ A) (f< : l ≤ₗ l')
-- -- -- -- -- -- --        → (∃ (λ BA' → [A] PE.≡ Bᵣ W BA')) TS.⊎ (∃ (λ BA' → [A] PE.≡ emb 0<1 (Bᵣ W BA')))
-- -- -- -- -- -- -- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ BA') f< = TS.inj₁ (BA' , PE.refl)
-- -- -- -- -- -- -- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ BA') f< = TS.inj₁ (BA' , PE.refl)
-- -- -- -- -- -- -- LogW1 BΣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΠ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- -- -- -- -- --   with (whrDet* ( red (wfRed≤* f< D) , Σₙ) (red D′ , Πₙ))
-- -- -- -- -- -- -- ... | ()
-- -- -- -- -- -- -- LogW1 BΠ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Bᵣ BΣ (Bᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′)) f<
-- -- -- -- -- -- --   with (whrDet* (red (wfRed≤* f< D) , Πₙ) (red D′ , Σₙ))
-- -- -- -- -- -- -- ... | ()
-- -- -- -- -- -- -- LogW1 {lε' = lε'} W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (U≢B W (whnfRed* {_} {_} {_} {lε'} (red (wfRed≤* f< D)) Uₙ))
-- -- -- -- -- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (ℕ≢B W (whrDet* (red x , ℕₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (Empty≢B W (whrDet* (red x , Emptyₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Unitᵣ x) f< =
-- -- -- -- -- -- --   ⊥-elim (Unit≢B W (whrDet* (red x , Unitₙ) (red (wfRed≤* f< D) , ⟦ W ⟧ₙ)))
-- -- -- -- -- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne (ne K D' neK K≡K)) f< =
-- -- -- -- -- -- --   ⊥-elim (B≢ne W neK (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red D' , ne neK)))
-- -- -- -- -- -- -- LogW1 W BA (emb 0<1 [A]) f< with LogW0 W BA [A] f<
-- -- -- -- -- -- -- LogW1 W BA (emb 0<1 [A]) f< | BA' , PE.refl = TS.inj₂ (BA' , PE.refl)
-- -- -- -- -- -- -- LogW1 W (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ϝᵣ mε A⇒B αB [B]t [B]f) f< =
-- -- -- -- -- -- --   ⊥-elim (B≢αne W αB (whrDet* (red (wfRed≤* f< D) , ⟦ W ⟧ₙ) (red A⇒B , αₙ αB)))
