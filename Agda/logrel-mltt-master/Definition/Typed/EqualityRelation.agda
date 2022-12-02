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
    _/_⊢_≅_   : Con Term n → LCon → (A B : Term n)   → Set

    -- Equality of terms
    _/_⊢_≅_∷_ : Con Term n → LCon → (t u A : Term n) → Set

    -- Equality of neutral terms
    _/_⊢_~_∷_ : Con Term n → LCon → (t u A : Term n) → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : Γ / l ⊢ k ~ j ∷ A
            → Γ / l ⊢ k ≅ j ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : Γ / l ⊢ A ≅ B
          → Γ / l ⊢ A ≡ B
    ≅ₜ-eq : Γ / l ⊢ t ≅ u ∷ A
          → Γ / l ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : Γ / l ⊢ A ≅ B ∷ U
           → Γ / l ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ / l ⊢ A ≅ B     → Γ / l ⊢ B ≅ A
    ≅ₜ-sym : Γ / l ⊢ t ≅ u ∷ A → Γ / l ⊢ u ≅ t ∷ A
    ~-sym  : Γ / l ⊢ k ~ j ∷ A → Γ / l ⊢ j ~ k ∷ A

    -- Transitivity
    ≅-trans  : Γ / l ⊢ A ≅ B     → Γ / l ⊢ B ≅ C     → Γ / l ⊢ A ≅ C
    ≅ₜ-trans : Γ / l ⊢ t ≅ u ∷ A → Γ / l ⊢ u ≅ v ∷ A → Γ / l ⊢ t ≅ v ∷ A
    ~-trans  : Γ / l ⊢ k ~ j ∷ A → Γ / l ⊢ j ~ m ∷ A → Γ / l ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : Γ / l ⊢ t ≅ u ∷ A → Γ / l ⊢ A ≡ B → Γ / l ⊢ t ≅ u ∷ B
    ~-conv : Γ / l ⊢ k ~ j ∷ A → Γ / l ⊢ A ≡ B → Γ / l ⊢ k ~ j ∷ B

    -- Weakening
    ≅-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / l
          → Γ / l ⊢ A ≅ B
          → Δ / l ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / l
          → Γ / l ⊢ t ≅ u ∷ A
          → Δ / l ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ / l
          → Γ / l ⊢ k ~ j ∷ A
          → Δ / l ⊢ wk ρ k ~ wk ρ j ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ / l ⊢ A ⇒* A′
          → Γ / l ⊢ B ⇒* B′
          → Whnf {l} A′
          → Whnf {l} B′
          → Γ / l ⊢ A′ ≅ B′
          → Γ / l ⊢ A  ≅ B

    ≅ₜ-red : Γ / l ⊢ A ⇒* B
           → Γ / l ⊢ a ⇒* a′ ∷ B
           → Γ / l ⊢ b ⇒* b′ ∷ B
           → Whnf {l} B
           → Whnf {l} a′
           → Whnf {l} b′
           → Γ / l ⊢ a′ ≅ b′ ∷ B
           → Γ / l ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ⊢ Γ / l → Γ / l ⊢ U ≅ U

    -- Natural number type reflexivity
    ≅-ℕrefl   : ⊢ Γ / l → Γ / l ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ⊢ Γ / l → Γ / l ⊢ ℕ ≅ ℕ ∷ U

    -- Empty type reflexivity
    ≅-Emptyrefl   : ⊢ Γ / l → Γ / l ⊢ Empty ≅ Empty
    ≅ₜ-Emptyrefl  : ⊢ Γ / l → Γ / l ⊢ Empty ≅ Empty ∷ U

    -- Unit type reflexivity
    ≅-Unitrefl   : ⊢ Γ / l → Γ / l ⊢ Unit ≅ Unit
    ≅ₜ-Unitrefl  : ⊢ Γ / l → Γ / l ⊢ Unit ≅ Unit ∷ U

    -- Unit η-equality
    ≅ₜ-η-unit : Γ / l ⊢ e ∷ Unit
              → Γ / l ⊢ e′ ∷ Unit
              → Γ / l ⊢ e ≅ e′ ∷ Unit

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E}
              → Γ / l ⊢ F
              → Γ / l ⊢ F ≅ H
              → Γ ∙ F / l ⊢ G ≅ E
              → Γ / l ⊢ Π F ▹ G ≅ Π H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E}
              → Γ / l ⊢ F
              → Γ / l ⊢ F ≅ H ∷ U
              → Γ ∙ F / l ⊢ G ≅ E ∷ U
              → Γ / l ⊢ Π F ▹ G ≅ Π H ▹ E ∷ U

    -- Σ-congruence

    ≅-Σ-cong  : ∀ {F G H E}
              → Γ / l ⊢ F
              → Γ / l ⊢ F ≅ H
              → Γ ∙ F / l ⊢ G ≅ E
              → Γ / l ⊢ Σ F ▹ G ≅ Σ H ▹ E

    ≅ₜ-Σ-cong : ∀ {F G H E}
              → Γ / l ⊢ F
              → Γ / l ⊢ F ≅ H ∷ U
              → Γ ∙ F / l ⊢ G ≅ E ∷ U
              → Γ / l ⊢ Σ F ▹ G ≅ Σ H ▹ E ∷ U

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ / l → Γ / l ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ / l ⊢ m ≅ n ∷ ℕ → Γ / l ⊢ suc m ≅ suc n ∷ ℕ

    -- α congruence
    ≅-α-cong : ∀ {m n} → Γ / l ⊢ m ≅ n ∷ ℕ → Γ / l ⊢ α m ≅ α n ∷ 𝔹

    -- true reflexivity
    ≅ₜ-truerefl : ⊢ Γ / l → Γ / l ⊢ true ≅ true ∷ 𝔹
    
    -- false reflexivity
    ≅ₜ-falserefl : ⊢ Γ / l → Γ / l ⊢ false ≅ false ∷ 𝔹

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ / l ⊢ F
           → Γ / l ⊢ f ∷ Π F ▹ G
           → Γ / l ⊢ g ∷ Π F ▹ G
           → Function f
           → Function g
           → Γ ∙ F / l ⊢ wk1 f ∘ var x0 ≅ wk1 g ∘ var x0 ∷ G
           → Γ / l ⊢ f ≅ g ∷ Π F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {p r F G}
          → Γ / l ⊢ F
          → Γ ∙ F / l ⊢ G
          → Γ / l ⊢ p ∷ Σ F ▹ G
          → Γ / l ⊢ r ∷ Σ F ▹ G
          → Product p
          → Product r
          → Γ / l ⊢ fst p ≅ fst r ∷ F
          → Γ / l ⊢ snd p ≅ snd r ∷ G [ fst p ]
          → Γ / l ⊢ p ≅ r ∷ Σ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ / l ⊢ var x ∷ A → Γ / l ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ / l ⊢ f ~ g ∷ Π F ▹ G
          → Γ / l ⊢ a ≅ b ∷ F
          → Γ / l ⊢ f ∘ a ~ g ∘ b ∷ G [ a ]

    -- Product projections congruence
    ~-fst : ∀ {p r F G}
          → Γ / l ⊢ F
          → Γ ∙ F / l ⊢ G
          → Γ / l ⊢ p ~ r ∷ Σ F ▹ G
          → Γ / l ⊢ fst p ~ fst r ∷ F

    ~-snd : ∀ {p r F G}
          → Γ / l ⊢ F
          → Γ ∙ F / l ⊢ G
          → Γ / l ⊢ p ~ r ∷ Σ F ▹ G
          → Γ / l ⊢ snd p ~ snd r ∷ G [ fst p ]

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ / l ⊢ F ≅ F′
             → Γ  / l    ⊢ z ≅ z′ ∷ F [ zero ]
             → Γ / l     ⊢ s ≅ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
             → Γ / l     ⊢ n ~ n′ ∷ ℕ
             → Γ / l     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ]
             
    -- Boolean recursion congruence
    ~-boolrec : ∀ {t t′ f f′ b b′ F F′}
             → Γ ∙ 𝔹 / l ⊢ F ≅ F′
             → Γ  / l    ⊢ t ≅ t′ ∷ F [ true ]
             → Γ  / l    ⊢ f ≅ f′ ∷ F [ false ]
             → Γ / l     ⊢ b ~ b′ ∷ 𝔹
             → Γ / l     ⊢ boolrec F t f b ~ boolrec F′ t′ f′ b′ ∷ F [ b ]

    -- Empty recursion congruence
    ~-Emptyrec : ∀ {n n′ F F′}
               → Γ / l ⊢ F ≅ F′
               → Γ / l ⊢ n ~ n′ ∷ Empty
               → Γ / l ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F

    -- Fascist congruence on types
    ≅-ϝ : ∀ {n A B}    → Γ / (addₗ n Btrue l)  ⊢ A ≅ B
                       → Γ / (addₗ n Bfalse l) ⊢ A ≅ B
                       → Γ / l                ⊢ A ≅ B
  
    -- Fascist congruence on terms
    ≅ₜ-ϝ : ∀ {n t u A}  → Γ / (addₗ n Btrue l)  ⊢ t ≅ u ∷ A
                       → Γ / (addₗ n Bfalse l) ⊢ t ≅ u ∷ A
                       → Γ / l                ⊢ t ≅ u ∷ A

-- Fascist congruence on neutrals
    ~-ϝ : ∀ {n t u A}  → Γ / (addₗ n Btrue l)  ⊢ t ~ u ∷ A
                       → Γ / (addₗ n Bfalse l) ⊢ t ~ u ∷ A
                       → Γ / l                ⊢ t ~ u ∷ A

  -- Star reflexivity
  ≅ₜ-starrefl : ⊢ Γ / l → Γ / l ⊢ star ≅ star ∷ Unit
  ≅ₜ-starrefl [Γ] = ≅ₜ-η-unit (starⱼ [Γ]) (starⱼ [Γ])

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k j} → Γ / l ⊢ k ~ j ∷ U → Γ / l ⊢ k ≅ j
  ~-to-≅ k~j = ≅-univ (~-to-≅ₜ k~j)


  ≅-W-cong : ∀ {F G H E} W
          → Γ / l ⊢ F
          → Γ / l ⊢ F ≅ H
          → Γ ∙ F / l ⊢ G ≅ E
          → Γ / l ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong BΠ = ≅-Π-cong
  ≅-W-cong BΣ = ≅-Σ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ / l ⊢ F
            → Γ / l ⊢ F ≅ H ∷ U
            → Γ ∙ F / l ⊢ G ≅ E ∷ U
            → Γ / l ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U
  ≅ₜ-W-cong BΠ = ≅ₜ-Π-cong
  ≅ₜ-W-cong BΣ = ≅ₜ-Σ-cong
