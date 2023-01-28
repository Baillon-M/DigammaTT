{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)

open import Tools.Fin
open import Tools.Nat

private
  variable
    ℓ n : Nat
    Γ : Con Term n
    Δ : Con Term ℓ
    l : LCon
    lε : ⊢ₗ l
    ρ : Wk ℓ n
    A A′ B B′ C : Term n
    a a′ b b′ e e′ : Term n
    j k m t u v : Term n

-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _/_⊢_≅_   : Con Term n → {l : LCon} → ⊢ₗ l → (A B : Term n)   → Set

    -- Equality of terms
    _/_⊢_≅_∷_ : Con Term n → {l : LCon} → ⊢ₗ l → (t u A : Term n) → Set

    -- Equality of neutral terms
    _/_⊢_~_∷_ : Con Term n → {l : LCon} → ⊢ₗ l → (t u A : Term n) → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : Γ / lε ⊢ k ~ j ∷ A
            → Γ / lε ⊢ k ≅ j ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : Γ / lε ⊢ A ≅ B
          → Γ / lε ⊢ A ≡ B
    ≅ₜ-eq : Γ / lε ⊢ t ≅ u ∷ A
          → Γ / lε ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : Γ / lε ⊢ A ≅ B ∷ U
           → Γ / lε ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ / lε ⊢ A ≅ B     → Γ / lε ⊢ B ≅ A
    ≅ₜ-sym : Γ / lε ⊢ t ≅ u ∷ A → Γ / lε ⊢ u ≅ t ∷ A
    ~-sym  : Γ / lε ⊢ k ~ j ∷ A → Γ / lε ⊢ j ~ k ∷ A

    -- Transitivity
    ≅-trans  : Γ / lε ⊢ A ≅ B     → Γ / lε ⊢ B ≅ C     → Γ / lε ⊢ A ≅ C
    ≅ₜ-trans : Γ / lε ⊢ t ≅ u ∷ A → Γ / lε ⊢ u ≅ v ∷ A → Γ / lε ⊢ t ≅ v ∷ A
    ~-trans  : Γ / lε ⊢ k ~ j ∷ A → Γ / lε ⊢ j ~ m ∷ A → Γ / lε ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : Γ / lε ⊢ t ≅ u ∷ A → Γ / lε ⊢ A ≡ B → Γ / lε ⊢ t ≅ u ∷ B
    ~-conv : Γ / lε ⊢ k ~ j ∷ A → Γ / lε ⊢ A ≡ B → Γ / lε ⊢ k ~ j ∷ B

    -- Weakening
    ≅-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / lε
          → Γ / lε ⊢ A ≅ B
          → Δ / lε ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / lε
          → Γ / lε ⊢ t ≅ u ∷ A
          → Δ / lε ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / lε
          → Γ / lε ⊢ k ~ j ∷ A
          → Δ / lε ⊢ wk ρ k ~ wk ρ j ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ / lε ⊢ A ⇒* A′
          → Γ / lε ⊢ B ⇒* B′
          → Whnf {l} {lε} A′
          → Whnf {l} {lε} B′
          → Γ / lε ⊢ A′ ≅ B′
          → Γ / lε ⊢ A  ≅ B

    ≅ₜ-red : Γ / lε ⊢ A ⇒* B
           → Γ / lε ⊢ a ⇒* a′ ∷ B
           → Γ / lε ⊢ b ⇒* b′ ∷ B
           → Whnf {l} {lε} B
           → Whnf {l} {lε} a′
           → Whnf {l} {lε} b′
           → Γ / lε ⊢ a′ ≅ b′ ∷ B
           → Γ / lε ⊢ a  ≅ b  ∷ A
           
    ≅ₜ-red₂ : Γ / lε ⊢ A ⇒* B
           → Γ / lε ⊢ a ⇒* a′ ∷ B
           → Γ / lε ⊢ b ⇒* b′ ∷ B
           → Γ / lε ⊢ a′ ≅ b′ ∷ B
           → Γ / lε ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ⊢ Γ / lε → Γ / lε ⊢ U ≅ U

    -- Natural number type reflexivity
    ≅-ℕrefl   : ⊢ Γ / lε → Γ / lε ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ⊢ Γ / lε → Γ / lε ⊢ ℕ ≅ ℕ ∷ U

    -- Boolean type reflexivity
    ≅-𝔹refl   : ⊢ Γ / lε → Γ / lε ⊢ 𝔹 ≅ 𝔹
    ≅ₜ-𝔹refl  : ⊢ Γ / lε → Γ / lε ⊢ 𝔹 ≅ 𝔹 ∷ U

    -- Empty type reflexivity
--    ≅-Emptyrefl   : ⊢ Γ / lε → Γ / lε ⊢ Empty ≅ Empty
--    ≅ₜ-Emptyrefl  : ⊢ Γ / lε → Γ / lε ⊢ Empty ≅ Empty ∷ U

    -- Unit type reflexivity
--    ≅-Unitrefl   : ⊢ Γ / lε → Γ / lε ⊢ Unit ≅ Unit
--    ≅ₜ-Unitrefl  : ⊢ Γ / lε → Γ / lε ⊢ Unit ≅ Unit ∷ U

    -- Unit η-equality
--    ≅ₜ-η-unit : Γ / lε ⊢ e ∷ Unit
--              → Γ / lε ⊢ e′ ∷ Unit
--              → Γ / lε ⊢ e ≅ e′ ∷ Unit

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E}
              → Γ / lε ⊢ F
              → Γ / lε ⊢ F ≅ H
              → Γ ∙ F / lε ⊢ G ≅ E
              → Γ / lε ⊢ Π F ▹ G ≅ Π H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E}
              → Γ / lε ⊢ F
              → Γ / lε ⊢ F ≅ H ∷ U
              → Γ ∙ F / lε ⊢ G ≅ E ∷ U
              → Γ / lε ⊢ Π F ▹ G ≅ Π H ▹ E ∷ U

    -- Σ-congruence

    ≅-Σ-cong  : ∀ {F G H E}
              → Γ / lε ⊢ F
              → Γ / lε ⊢ F ≅ H
              → Γ ∙ F / lε ⊢ G ≅ E
              → Γ / lε ⊢ Σ F ▹ G ≅ Σ H ▹ E

    ≅ₜ-Σ-cong : ∀ {F G H E}
              → Γ / lε ⊢ F
              → Γ / lε ⊢ F ≅ H ∷ U
              → Γ ∙ F / lε ⊢ G ≅ E ∷ U
              → Γ / lε ⊢ Σ F ▹ G ≅ Σ H ▹ E ∷ U

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ / lε → Γ / lε ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ / lε ⊢ m ≅ n ∷ ℕ → Γ / lε ⊢ suc m ≅ suc n ∷ ℕ

    -- α congruence
    ≅-α-cong : ∀ {m n} → Γ / lε ⊢ m ≅ n ∷ ℕ → Γ / lε ⊢ α m ≅ α n ∷ 𝔹

    -- true reflexivity
    ≅ₜ-truerefl : ⊢ Γ / lε → Γ / lε ⊢ true ≅ true ∷ 𝔹
    
    -- false reflexivity
    ≅ₜ-falserefl : ⊢ Γ / lε → Γ / lε ⊢ false ≅ false ∷ 𝔹

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ / lε ⊢ F
           → Γ / lε ⊢ f ∷ Π F ▹ G
           → Γ / lε ⊢ g ∷ Π F ▹ G
           → Function {_} {l} {lε} f
           → Function {_} {l} {lε} g
           → Γ ∙ F / lε ⊢ wk1 f ∘ var x0 ≅ wk1 g ∘ var x0 ∷ G
           → Γ / lε ⊢ f ≅ g ∷ Π F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {p r F G}
          → Γ / lε ⊢ F
          → Γ ∙ F / lε ⊢ G
          → Γ / lε ⊢ p ∷ Σ F ▹ G
          → Γ / lε ⊢ r ∷ Σ F ▹ G
          → Product p
          → Product r
          → Γ / lε ⊢ fst p ≅ fst r ∷ F
          → Γ / lε ⊢ snd p ≅ snd r ∷ G [ fst p ]
          → Γ / lε ⊢ p ≅ r ∷ Σ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ / lε ⊢ var x ∷ A → Γ / lε ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ / lε ⊢ f ~ g ∷ Π F ▹ G
          → Γ / lε ⊢ a ≅ b ∷ F
          → Γ / lε ⊢ f ∘ a ~ g ∘ b ∷ G [ a ]

    -- Product projections congruence
    ~-fst : ∀ {p r F G}
          → Γ / lε ⊢ F
          → Γ ∙ F / lε ⊢ G
          → Γ / lε ⊢ p ~ r ∷ Σ F ▹ G
          → Γ / lε ⊢ fst p ~ fst r ∷ F

    ~-snd : ∀ {p r F G}
          → Γ / lε ⊢ F
          → Γ ∙ F / lε ⊢ G
          → Γ / lε ⊢ p ~ r ∷ Σ F ▹ G
          → Γ / lε ⊢ snd p ~ snd r ∷ G [ fst p ]

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ / lε ⊢ F ≅ F′
             → Γ  / lε    ⊢ z ≅ z′ ∷ F [ zero ]
             → Γ / lε     ⊢ s ≅ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
             → Γ / lε     ⊢ n ~ n′ ∷ ℕ
             → Γ / lε     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ]
             
    -- Boolean recursion congruence
    ~-boolrec : ∀ {t t′ f f′ b b′ F F′}
             → Γ ∙ 𝔹 / lε ⊢ F ≅ F′
             → Γ  / lε    ⊢ t ≅ t′ ∷ F [ true ]
             → Γ  / lε    ⊢ f ≅ f′ ∷ F [ false ]
             → Γ / lε     ⊢ b ~ b′ ∷ 𝔹
             → Γ / lε     ⊢ boolrec F t f b ~ boolrec F′ t′ f′ b′ ∷ F [ b ]

    -- Empty recursion congruence
--    ~-Emptyrec : ∀ {n n′ F F′}
--               → Γ / lε ⊢ F ≅ F′
--               → Γ / lε ⊢ n ~ n′ ∷ Empty
--               → Γ / lε ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F

    -- Fascist congruence on types
    ≅-ϝ : ∀ {n nε A B}    → Γ / ⊢ₗ• l lε n Btrue nε  ⊢ A ≅ B
                          → Γ / ⊢ₗ• l lε n Bfalse nε  ⊢ A ≅ B
                          → Γ / lε                ⊢ A ≅ B
  
    -- Fascist congruence on terms
    ≅ₜ-ϝ : ∀ {n nε t u A}  → Γ / ⊢ₗ• l lε n Btrue nε   ⊢ t ≅ u ∷ A
                       → Γ / ⊢ₗ• l lε n Bfalse nε  ⊢ t ≅ u ∷ A
                       → Γ / lε                ⊢ t ≅ u ∷ A

-- Fascist congruence on neutrals
    ~-ϝ : ∀ {n nε t u A}  → Γ / ⊢ₗ• l lε n Btrue nε   ⊢ t ~ u ∷ A
                          → Γ / ⊢ₗ• l lε n Bfalse nε  ⊢ t ~ u ∷ A
                          → Γ / lε                ⊢ t ~ u ∷ A
-- Prefascist congruence on types
    ≅-τ : ∀ {n b nε A B}    → Γ / lε               ⊢ A ≅ B
                            → Γ / ⊢ₗ• l lε n b nε  ⊢ A ≅ B
-- Prefascist congruence on terms
    ≅ₜ-τ : ∀ {n b nε t u A}   → Γ / lε                ⊢ t ≅ u ∷ A
                             → Γ / ⊢ₗ• l lε n b nε   ⊢ t ≅ u ∷ A
-- Prefascist congruence on neutrals
    ~-τ : ∀ {n b nε t u A}    → Γ / lε               ⊢ t ~ u ∷ A
                            → Γ / ⊢ₗ• l lε n b nε  ⊢ t ~ u ∷ A
-- Permutation congruence on types
    ≅-≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A B}
               → l ≤ₗ l'
               → Γ / lε   ⊢ A ≅ B
               → Γ / lε'  ⊢ A ≅ B
               
-- Permutation congruence on terms
    ≅ₜ-≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t u A}
                → Γ / lε    ⊢ t ≅ u ∷ A
                → l ≤ₗ l'
                → Γ / lε'   ⊢ t ≅ u ∷ A
                             
-- Permutation congruence on neutrals
    ~-≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t u A}
               → l ≤ₗ l'
               → Γ / lε   ⊢ t ~ u ∷ A
               → Γ / lε'  ⊢ t ~ u ∷ A
  
  -- Star reflexivity
--  ≅ₜ-starrefl : ⊢ Γ / lε → Γ / lε ⊢ star ≅ star ∷ Unit
--  ≅ₜ-starrefl [Γ] = ≅ₜ-η-unit (starⱼ [Γ]) (starⱼ [Γ])

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k j} → Γ / lε ⊢ k ~ j ∷ U → Γ / lε ⊢ k ≅ j
  ~-to-≅ k~j = ≅-univ (~-to-≅ₜ k~j)


  ≅-W-cong : ∀ {F G H E} W
          → Γ / lε ⊢ F
          → Γ / lε ⊢ F ≅ H
          → Γ ∙ F / lε ⊢ G ≅ E
          → Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong BΠ = ≅-Π-cong
  ≅-W-cong BΣ = ≅-Σ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ / lε ⊢ F
            → Γ / lε ⊢ F ≅ H ∷ U
            → Γ ∙ F / lε ⊢ G ≅ E ∷ U
            → Γ / lε ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U
  ≅ₜ-W-cong BΠ = ≅ₜ-Π-cong
  ≅ₜ-W-cong BΣ = ≅ₜ-Σ-cong
