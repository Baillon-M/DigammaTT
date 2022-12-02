{-# OPTIONS --without-K --safe #-}

module Definition.Typed where

open import Definition.Untyped hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

infixl 30 _∙_
infix 30 Πⱼ_▹_
infix 30 Σⱼ_▹_
infix 30 ⟦_⟧ⱼ_/_▹_


private
  variable
    n m : Nat
    Γ  : Con Term n
    A B F : Term n
    G : Term (1+ n)
    x : Fin n


-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term n) (Γ : Con Term n) → Set where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)

mutual
  -- Well-formed context
  data ⊢_/_ : Con Term n → LCon → Set where
    ε   : ∀ {l} → ⊢ ε / l
    _∙_ : ∀ {l} → ⊢ Γ / l
          → Γ / l ⊢ A
          → ⊢ Γ ∙ A / l
    ϝ   : ∀ {l n}
          → ⊢ Γ / (addₗ n Btrue l)
          → ⊢ Γ / (addₗ n Bfalse l)
          → ⊢ Γ / l
--    τ   : ∀ {l n b}
--          → ⊢ Γ / l
--          → ⊢ Γ / (addₗ n b l)
--     π   : ∀ {l n1 n2 b1 b2}
--           → ⊢ Γ / (addₗ n1 b1 (addₗ n2 b2 l))
--           → ⊢ Γ / (addₗ n2 b2 (addₗ n1 b1 l))
          
  -- Well-formed type
  data _/_⊢_ (Γ : Con Term n) : ∀ (l : LCon) → Term n → Set where
    Uⱼ     : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ U
    ℕⱼ     : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ ℕ
    𝔹ⱼ     : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ 𝔹
    Emptyⱼ : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ Empty
    Unitⱼ  : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ Unit
    Πⱼ_▹_  : ∀ {l} → Γ / l     ⊢ F
           → Γ ∙ F / l ⊢ G
           → Γ / l     ⊢ Π F ▹ G
    Σⱼ_▹_  : ∀ {l} → Γ / l     ⊢ F
           → Γ ∙ F / l ⊢ G
           → Γ / l     ⊢ Σ F ▹ G
    univ   : ∀ {l} → Γ / l                ⊢ A ∷ U
           → Γ / l                        ⊢ A
    ϝⱼ :     ∀  {l F n}
           → Γ / (addₗ n Btrue l)          ⊢ F
           → Γ / (addₗ n Bfalse l)         ⊢ F
           → Γ / l                        ⊢ F
--    τⱼ   : ∀ {l n b A}
--          → Γ / l                         ⊢ A
--           → Γ / (addₗ n b l)               ⊢ A
--     πⱼ   : ∀ {l n1 n2 b1 b2 A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 l)) ⊢ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 l)) ⊢ A
          
  -- Well-formed term of a type
  data _/_⊢_∷_ (Γ : Con Term n) : ∀ (l : LCon) → Term n → Term n → Set where
    Πⱼ_▹_     : ∀ {l F G}
              → Γ / l     ⊢ F ∷ U
              → Γ ∙ F / l ⊢ G ∷ U
              → Γ / l     ⊢ Π F ▹ G ∷ U
    Σⱼ_▹_     : ∀ {l F G}
              → Γ / l     ⊢ F ∷ U
              → Γ ∙ F / l ⊢ G ∷ U
              → Γ / l     ⊢ Σ F ▹ G ∷ U
    ℕⱼ        : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ ℕ ∷ U
    𝔹ⱼ        : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ 𝔹 ∷ U
    Emptyⱼ    : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ Empty ∷ U
    Unitⱼ     : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ Unit ∷ U

    var       : ∀ {l A x}
              → ⊢ Γ / l
              → x ∷ A ∈ Γ
              → Γ / l ⊢ var x ∷ A

    lamⱼ      : ∀ {l F G t}
              → Γ / l     ⊢ F
              → Γ ∙ F / l ⊢ t ∷ G
              → Γ / l     ⊢ lam t ∷ Π F ▹ G
    _∘ⱼ_      : ∀ {l g a F G}
              → Γ / l ⊢     g ∷ Π F ▹ G
              → Γ / l ⊢     a ∷ F
              → Γ / l ⊢ g ∘ a ∷ G [ a ]

    prodⱼ     : ∀ {l F G t u}
              → Γ / l ⊢ F
              → Γ ∙ F / l ⊢ G
              → Γ / l ⊢ t ∷ F
              → Γ / l ⊢ u ∷ G [ t ]
              → Γ / l ⊢ prod t u ∷ Σ F ▹ G
    fstⱼ      : ∀ {l F G t}
              → Γ / l ⊢ F
              → Γ ∙ F / l ⊢ G
              → Γ / l ⊢ t ∷ Σ F ▹ G
              → Γ / l ⊢ fst t ∷ F
    sndⱼ      : ∀ {l F G t}
              → Γ / l ⊢ F
              → Γ ∙ F / l ⊢ G
              → Γ / l ⊢ t ∷ Σ F ▹ G
              → Γ / l ⊢ snd t ∷ G [ fst t ]

    zeroⱼ     : ∀ {l} → ⊢ Γ / l
              → Γ / l ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {l n}
              → Γ / l ⊢       n ∷ ℕ
              → Γ / l ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {l G s z n}
              → Γ ∙ ℕ / l ⊢ G
              → Γ / l       ⊢ z ∷ G [ zero ]
              → Γ / l       ⊢ s ∷ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
              → Γ / l       ⊢ n ∷ ℕ
              → Γ / l       ⊢ natrec G z s n ∷ G [ n ]

    trueⱼ     : ∀ {l} → ⊢ Γ / l
              → Γ / l ⊢ true ∷ 𝔹
    falseⱼ    : ∀ {l} → ⊢ Γ / l
              → Γ / l ⊢ false ∷ 𝔹
    boolrecⱼ   : ∀ {l G t f b}
              → Γ ∙ 𝔹 / l ⊢ G
              → Γ / l       ⊢ t ∷ G [ true ]
              → Γ / l       ⊢ f ∷ G [ false ]
              → Γ / l       ⊢ b ∷ 𝔹
              → Γ / l       ⊢ boolrec G t f b ∷ G [ b ]              
    Emptyrecⱼ : ∀ {l A e}
              → Γ / l ⊢ A → Γ / l ⊢ e ∷ Empty → Γ / l ⊢ Emptyrec A e ∷ A

    starⱼ     : ∀ {l} → ⊢ Γ / l → Γ / l ⊢ star ∷ Unit

    conv      : ∀ {l t A B}
              → Γ / l ⊢ t ∷ A
              → Γ / l ⊢ A ≡ B
              → Γ / l ⊢ t ∷ B
    αⱼ  : ∀ {l n}
              → Γ / l ⊢ n ∷ ℕ
              → Γ / l ⊢ α n ∷ 𝔹
    ϝⱼ :     ∀  {l t A n}
           → Γ / (addₗ n Btrue l)   ⊢ t ∷ A
           → Γ / (addₗ n Bfalse l)  ⊢ t ∷ A
           → Γ / l                 ⊢ t ∷ A
--    τⱼ   : ∀ {l n b t A}
--          → Γ / l                         ⊢ t ∷ A
--          → Γ / (addₗ n b l)               ⊢ t ∷ A
--     πⱼ   : ∀ {l n1 n2 b1 b2 t A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 l)) ⊢ t ∷ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 l)) ⊢ t ∷ A

  -- Type equality
  data _/_⊢_≡_ (Γ : Con Term n) : ∀ (l : LCon) → Term n → Term n → Set where
    univ   : ∀ {l A B}
           → Γ / l ⊢ A ≡ B ∷ U
           → Γ / l ⊢ A ≡ B
    refl   : ∀ {l A}
           → Γ / l ⊢ A
           → Γ / l ⊢ A ≡ A
    sym    : ∀ {l A B}
           → Γ / l ⊢ A ≡ B
           → Γ / l ⊢ B ≡ A
    trans  : ∀ {l A B C}
           → Γ / l ⊢ A ≡ B
           → Γ / l ⊢ B ≡ C
           → Γ / l ⊢ A ≡ C
    Π-cong : ∀ {l F H G E}
           → Γ / l     ⊢ F
           → Γ / l     ⊢ F ≡ H
           → Γ ∙ F / l ⊢ G ≡ E
           → Γ / l     ⊢ Π F ▹ G ≡ Π H ▹ E
    Σ-cong : ∀ {l F H G E}
           → Γ / l     ⊢ F
           → Γ / l     ⊢ F ≡ H
           → Γ ∙ F / l ⊢ G ≡ E
           → Γ / l     ⊢ Σ F ▹ G ≡ Σ H ▹ E
    ϝ-cong : ∀  {l F G n}
           → Γ / (addₗ n Btrue l)   ⊢ F ≡ G
           → Γ / (addₗ n Bfalse l)  ⊢ F ≡ G
           → Γ / l                 ⊢ F ≡ G
--    τⱼ   : ∀ {l n b A B}
--          → Γ / l                         ⊢ A ≡ B
--          → Γ / (addₗ n b l)               ⊢ A ≡ B
--     πⱼ   : ∀ {l n1 n2 b1 b2 A B}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 l)) ⊢ A ≡ B
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 l)) ⊢ A ≡ B

  -- Term equality
  data _/_⊢_≡_∷_ (Γ : Con Term n) : ∀ (l : LCon) → Term n → Term n → Term n → Set where
    refl          : ∀ {l t A}
                  → Γ / l ⊢ t ∷ A
                  → Γ / l ⊢ t ≡ t ∷ A
    sym           : ∀ {l t u A}
                  → Γ / l ⊢ t ≡ u ∷ A
                  → Γ / l ⊢ u ≡ t ∷ A
    trans         : ∀ {l t u r A}
                  → Γ / l ⊢ t ≡ u ∷ A
                  → Γ / l ⊢ u ≡ r ∷ A
                  → Γ / l ⊢ t ≡ r ∷ A
    conv          : ∀ {l A B t u}
                  → Γ / l ⊢ t ≡ u ∷ A
                  → Γ / l ⊢ A ≡ B
                  → Γ / l ⊢ t ≡ u ∷ B
    Π-cong        : ∀ {l E F G H}
                  → Γ / l     ⊢ F
                  → Γ / l     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F / l ⊢ G ≡ E       ∷ U
                  → Γ / l     ⊢ Π F ▹ G ≡ Π H ▹ E ∷ U
    Σ-cong        : ∀ {l E F G H}
                  → Γ / l     ⊢ F
                  → Γ / l    ⊢ F ≡ H       ∷ U
                  → Γ ∙ F / l ⊢ G ≡ E       ∷ U
                  → Γ / l     ⊢ Σ F ▹ G ≡ Σ H ▹ E ∷ U
    app-cong      : ∀ {l a b f g F G}
                  → Γ / l ⊢ f ≡ g ∷ Π F ▹ G
                  → Γ / l ⊢ a ≡ b ∷ F
                  → Γ / l ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    β-red         : ∀ {l a t F G}
                  → Γ / l     ⊢ F
                  → Γ ∙ F / l ⊢ t ∷ G
                  → Γ / l     ⊢ a ∷ F
                  → Γ / l     ⊢ (lam t) ∘ a ≡ t [ a ] ∷ G [ a ]
    η-eq          : ∀ {l f g F G}
                  → Γ / l     ⊢ F
                  → Γ / l     ⊢ f ∷ Π F ▹ G
                  → Γ / l     ⊢ g ∷ Π F ▹ G
                  → Γ ∙ F / l ⊢ wk1 f ∘ var x0 ≡ wk1 g ∘ var x0 ∷ G
                  → Γ / l     ⊢ f ≡ g ∷ Π F ▹ G
    fst-cong      : ∀ {l t t' F G}
                  → Γ / l ⊢ F
                  → Γ ∙ F / l ⊢ G
                  → Γ / l ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ / l ⊢ fst t ≡ fst t' ∷ F
    snd-cong      : ∀ {l t t' F G}
                  → Γ / l ⊢ F
                  → Γ ∙ F / l ⊢ G
                  → Γ / l ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ / l ⊢ snd t ≡ snd t' ∷ G [ fst t ]
    Σ-β₁          : ∀ {l F G t u}
                  → Γ / l ⊢ F
                  → Γ ∙ F / l ⊢ G
                  → Γ / l ⊢ t ∷ F
                  → Γ / l ⊢ u ∷ G [ t ]
                  → Γ / l ⊢ fst (prod t u) ≡ t ∷ F
    Σ-β₂          : ∀ {l F G t u}
                  → Γ / l ⊢ F
                  → Γ ∙ F / l ⊢ G
                  → Γ / l ⊢ t ∷ F
                  → Γ / l ⊢ u ∷ G [ t ]
                  → Γ / l ⊢ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]
    Σ-η           : ∀ {l p r F G}
                  → Γ / l ⊢ F
                  → Γ ∙ F / l ⊢ G
                  → Γ / l ⊢ p ∷ Σ F ▹ G
                  → Γ / l ⊢ r ∷ Σ F ▹ G
                  → Γ / l ⊢ fst p ≡ fst r ∷ F
                  → Γ / l ⊢ snd p ≡ snd r ∷ G [ fst p ]
                  → Γ / l ⊢ p ≡ r ∷ Σ F ▹ G
    suc-cong      : ∀ {l m n}
                  → Γ / l ⊢ m ≡ n ∷ ℕ
                  → Γ / l ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {l z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ / l ⊢ F ≡ F′
                  → Γ / l     ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ / l     ⊢ s ≡ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / l     ⊢ n ≡ n′ ∷ ℕ
                  → Γ / l     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {l z s F}
                  → Γ ∙ ℕ / l ⊢ F
                  → Γ / l     ⊢ z ∷ F [ zero ]
                  → Γ / l     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / l     ⊢ natrec F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {l n z s F}
                  → Γ / l     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ / l ⊢ F
                  → Γ / l     ⊢ z ∷ F [ zero ]
                  → Γ / l     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / l     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                          ∷ F [ suc n ]
    boolrec-cong   : ∀ {l t t′ f f′ b b′ F F′}
                  → Γ ∙ 𝔹 / l ⊢ F ≡ F′
                  → Γ / l     ⊢ t ≡ t′ ∷ F [ true ]
                  → Γ / l     ⊢ f ≡ f′ ∷ F [ false ]
                  → Γ / l     ⊢ b ≡ b′ ∷ 𝔹
                  → Γ / l     ⊢ boolrec F t f b ≡ boolrec F′ t′ f′ b′ ∷ F [ b ]
    boolrec-true   : ∀ {l t f F}
                  → Γ ∙ 𝔹 / l ⊢ F
                  → Γ / l     ⊢ t ∷ F [ true ]
                  → Γ / l     ⊢ f ∷ F [ false ]
                  → Γ / l     ⊢ boolrec F t f true ≡ t ∷ F [ true ]
    boolrec-false   : ∀ {l t f F}
                  → Γ ∙ 𝔹 / l ⊢ F
                  → Γ / l     ⊢ t ∷ F [ true ]
                  → Γ / l     ⊢ f ∷ F [ false ]
                  → Γ / l     ⊢ boolrec F t f false ≡ f ∷ F [ false ]
    Emptyrec-cong : ∀ {l A A' e e'}
                  → Γ / l ⊢ A ≡ A'
                  → Γ / l ⊢ e ≡ e' ∷ Empty
                  → Γ / l ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A
    η-unit        : ∀ {l e e'}
                  → Γ / l ⊢ e ∷ Unit
                  → Γ / l ⊢ e' ∷ Unit
                  → Γ / l ⊢ e ≡ e' ∷ Unit
    α-cong      : ∀ {l m n}
                  → Γ / l ⊢ m ≡ n ∷ ℕ
                  → Γ / l ⊢ α m ≡ α n ∷ 𝔹
    ϝ-cong      : ∀ {l A t u n}
                  → Γ / (addₗ n Btrue l)   ⊢ t ≡ u ∷ A
                  → Γ / (addₗ n Bfalse l)  ⊢ t ≡ u ∷ A
                  → Γ / l                 ⊢ t ≡ u ∷ A
    α-conv      : ∀ {l t b}
                   → Γ / l     ⊢ t ∷ ℕ
                   → (tε : InLCon t b l)
                   → Γ / l     ⊢ α t ≡ b ∷ 𝔹
--    α-convfalse     : ∀ {l n}
--                   → Γ / (addₗ n Bfalse l)      ⊢ (natToTerm _ n) ∷ ℕ
--                   → Γ / (addₗ n Bfalse l)     ⊢ α (natToTerm _ n) ≡ (BboolToTerm _ Bfalse) ∷ 𝔹
--    τⱼ   : ∀ {l n b t u A}
--          → Γ / l                         ⊢ t ≡ u ∷ A
--          → Γ / (addₗ n b l)               ⊢ t ≡ u ∷ A
--     πⱼ   : ∀ {l n1 n2 b1 b2 t u A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 l)) ⊢ t ≡ u ∷ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 l)) ⊢ t ≡ u ∷ A




mutual
  ConPerm : ∀ l n
           → ⊢ Γ / l
           → ⊢ Γ / (permut n l)
  ConPerm l n ε = ε
  ConPerm l n (⊢Γ ∙ ⊢A) = ConPerm l n  ⊢Γ ∙ TyPerm l n ⊢A
  ConPerm l n (ϝ g d) = ϝ (ConPerm _ (1+ n) g) (ConPerm _ (1+ n) d)

  TyPerm : ∀ l n
           → Γ / l ⊢ A
           → Γ / (permut n l) ⊢ A
  TyPerm l n (Uⱼ ⊢Γ) = Uⱼ (ConPerm l n ⊢Γ) 
  TyPerm l n (ℕⱼ ⊢Γ) = ℕⱼ (ConPerm l n ⊢Γ)
  TyPerm l n (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (ConPerm l n ⊢Γ)
  TyPerm l n (Emptyⱼ ⊢Γ) = Emptyⱼ (ConPerm l n ⊢Γ)
  TyPerm l n (Unitⱼ ⊢Γ) = Unitⱼ (ConPerm l n ⊢Γ)
  TyPerm l n (Πⱼ A ▹ B) = Πⱼ TyPerm l n A ▹ TyPerm l n B
  TyPerm l n (Σⱼ A ▹ B) = Σⱼ TyPerm l n A ▹ TyPerm l n B
  TyPerm l n (univ u) = univ (TermPerm l n u)
  TyPerm l n (ϝⱼ g d) = ϝⱼ (TyPerm _ (1+ n) g) (TyPerm _ (1+ n) d)

  TermPerm : ∀ l n {t}
           → Γ / l ⊢ t ∷ A
           → Γ / (permut n l) ⊢ t ∷ A
  TermPerm l n (ℕⱼ ⊢Γ) = ℕⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (Emptyⱼ ⊢Γ) = Emptyⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (Unitⱼ ⊢Γ) = Unitⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (Πⱼ A ▹ B) = Πⱼ TermPerm l n A ▹ TermPerm l n B
  TermPerm l n (Σⱼ A ▹ B) = Σⱼ TermPerm l n A ▹ TermPerm l n B
  TermPerm l n (var ⊢Γ x) = var (ConPerm l n ⊢Γ) x
  TermPerm l n (lamⱼ ⊢F x) = lamⱼ (TyPerm l n ⊢F) (TermPerm l n x)
  TermPerm l n (t ∘ⱼ u) = TermPerm l n t ∘ⱼ TermPerm l n u
  TermPerm l n (prodⱼ x x₁ x₂ x₃) = prodⱼ (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  TermPerm l n (fstⱼ x x₁ x₂) = fstⱼ (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂)
  TermPerm l n (sndⱼ x x₁ x₂) = sndⱼ (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂)
  TermPerm l n (zeroⱼ ⊢Γ) = zeroⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (sucⱼ ⊢n) = sucⱼ (TermPerm l n ⊢n)
  TermPerm l n (natrecⱼ x x₁ x₂ x₃) = natrecⱼ (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  TermPerm l n (trueⱼ ⊢Γ) = trueⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (falseⱼ ⊢Γ) = falseⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (boolrecⱼ x x₁ x₂ x₃) = boolrecⱼ (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  TermPerm l n (Emptyrecⱼ x x₁) = Emptyrecⱼ (TyPerm l n x) (TermPerm l n x₁)
  TermPerm l n (starⱼ ⊢Γ) = starⱼ (ConPerm l n ⊢Γ)
  TermPerm l n (conv x x₁) = conv (TermPerm l n x) (ConvTyPerm l n x₁)
  TermPerm l n (αⱼ x) = αⱼ (TermPerm l n x)
  TermPerm l n (ϝⱼ g d) = ϝⱼ (TermPerm _ (1+ n) g) (TermPerm _ (1+ n) d)

  ConvTyPerm : ∀ l n {A B}
             → Γ / l ⊢ A ≡ B
             → Γ / permut n l ⊢ A ≡ B
  ConvTyPerm l n (univ t≡u) = univ (ConvTermPerm l n t≡u)
  ConvTyPerm l n (refl A) = refl (TyPerm l n A)
  ConvTyPerm l n (sym A) = sym (ConvTyPerm l n A)
  ConvTyPerm l n (trans t≡u u≡v) = trans (ConvTyPerm l n t≡u) (ConvTyPerm l n u≡v)
  ConvTyPerm l n (Π-cong x x₁ x₂) = Π-cong (TyPerm l n x) (ConvTyPerm l n x₁) (ConvTyPerm l n x₂)
  ConvTyPerm l n (Σ-cong x x₁ x₂) = Σ-cong (TyPerm l n x) (ConvTyPerm l n x₁) (ConvTyPerm l n x₂)
  ConvTyPerm l n (ϝ-cong g d) = ϝ-cong (ConvTyPerm _ (1+ n) g) (ConvTyPerm _ (1+ n) d)

  ConvTermPerm : ∀ l n {A t u}
               → Γ / l ⊢ t ≡ u ∷ A
               → Γ / permut n l ⊢ t ≡ u ∷ A
  ConvTermPerm l n (refl t) = refl (TermPerm l n t)
  ConvTermPerm l n (sym x) = sym (ConvTermPerm l n x)
  ConvTermPerm l n (trans x x₁) = trans (ConvTermPerm l n x) (ConvTermPerm l n x₁)
  ConvTermPerm l n (conv x x₁) = conv (ConvTermPerm l n x) (ConvTyPerm l n x₁)
  ConvTermPerm l n (Π-cong x x₁ x₂) = Π-cong (TyPerm l n x) (ConvTermPerm l n x₁) (ConvTermPerm l n x₂)
  ConvTermPerm l n (Σ-cong x x₁ x₂) = Σ-cong (TyPerm l n x) (ConvTermPerm l n x₁) (ConvTermPerm l n x₂)
  ConvTermPerm l n (app-cong x x₁) = app-cong (ConvTermPerm l n x) (ConvTermPerm l n x₁)
  ConvTermPerm l n (β-red x x₁ x₂) = β-red (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂)
  ConvTermPerm l n (η-eq x x₁ x₂ x₃) = η-eq (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂) (ConvTermPerm l n x₃)
  ConvTermPerm l n (fst-cong x x₁ x₂) = fst-cong (TyPerm l n x) (TyPerm l n x₁) (ConvTermPerm l n x₂)
  ConvTermPerm l n (snd-cong x x₁ x₂) = snd-cong (TyPerm l n x) (TyPerm l n x₁) (ConvTermPerm l n x₂)
  ConvTermPerm l n (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  ConvTermPerm l n (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  ConvTermPerm l n (Σ-η x x₁ x₂ x₃ x₄ x₅) = Σ-η (TyPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃) (ConvTermPerm l n x₄) (ConvTermPerm l n x₅)
  ConvTermPerm l n (suc-cong x) = suc-cong (ConvTermPerm l n x)
  ConvTermPerm l n (natrec-cong x x₁ x₂ x₃) = natrec-cong (ConvTyPerm l n x) (ConvTermPerm l n x₁) (ConvTermPerm l n x₂) (ConvTermPerm l n x₃)
  ConvTermPerm l n (natrec-zero x x₁ x₂) = natrec-zero (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂)
  ConvTermPerm l n (natrec-suc x x₁ x₂ x₃) = natrec-suc (TermPerm l n x) (TyPerm l n x₁) (TermPerm l n x₂) (TermPerm l n x₃)
  ConvTermPerm l n (boolrec-cong x x₁ x₂ x₃) = boolrec-cong (ConvTyPerm l n x) (ConvTermPerm l n x₁) (ConvTermPerm l n x₂) (ConvTermPerm l n x₃)
  ConvTermPerm l n (boolrec-true x x₁ x₂) = boolrec-true (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂)
  ConvTermPerm l n (boolrec-false x x₁ x₂) = boolrec-false (TyPerm l n x) (TermPerm l n x₁) (TermPerm l n x₂)
  ConvTermPerm l n (Emptyrec-cong x x₁) = Emptyrec-cong (ConvTyPerm l n x) (ConvTermPerm l n x₁)
  ConvTermPerm l n (η-unit x x₁) = η-unit (TermPerm l n x) (TermPerm l n x₁)
  ConvTermPerm l n (α-cong x) = α-cong (ConvTermPerm l n x)
  ConvTermPerm l n (ϝ-cong g d) = ϝ-cong (ConvTermPerm _ (1+ n) g) (ConvTermPerm _ (1+ n) d)
  ConvTermPerm (addₗ t b εₗ) 0 (α-conv x (InHere t b εₗ)) = α-conv (TermPerm _ 0 x) (InHere _ b εₗ)  
  ConvTermPerm (addₗ t1 b1 (addₗ t2 b2 l)) 0 (α-conv x (InHere t1 b1 _)) = α-conv (TermPerm _ 0 x) (InThere _ _ _ (InHere _ _ _) t2 b2)
  ConvTermPerm _ 0 (α-conv x (InThere _ _ .(addₗ t b l) (InHere t b l) _ _)) = α-conv (TermPerm _ 0 x) (InHere _ _ _)
  ConvTermPerm (addₗ n1 b1 (addₗ n2 b2 l)) 0 (α-conv x (InThere _ _ .(addₗ _ _ l) (InThere _ _ .l x₄ _ _) _ _)) = α-conv (TermPerm _ 0 x) (InThere _ _ _ (InThere _ _ _ x₄ _ _) _ _)
  ConvTermPerm (addₗ n1 b εₗ) (1+ n) (α-conv x (InHere t b _)) = α-conv (TermPerm _ (1+ n) x) (InHere _ _ _)
  ConvTermPerm (addₗ n1 b2 l) (1+ n) (α-conv x (InThere _ _ .l x₂ _ _)) = α-conv (TermPerm _ (1+ n) x) (InThere _ _ _ (permutInLCon _ _ _ _ x₂) _ _)
  ConvTermPerm (addₗ n1 b1 (addₗ n2 b2 l)) (1+ n) (α-conv x (InHere _ _ _)) = α-conv (TermPerm _ (1+ n) x) (InHere _ b1 _)


mutual
  τCon : ∀ l n b
           → ⊢ Γ / l
           → ⊢ Γ / (addₗ n b l)
  τCon l n b ε = ε
  τCon l n b (⊢Γ ∙ ⊢A) = τCon l n b ⊢Γ ∙ τTy l n b ⊢A
  τCon l n b (ϝ g d) = ϝ (ConPerm (addₗ n b (addₗ _ Btrue l)) 0 (τCon _ n b g)) (ConPerm (addₗ n b (addₗ _ Bfalse l)) 0 (τCon _ n b d))

  τTy : ∀ l n b
           → Γ / l ⊢ A
           → Γ / (addₗ n b l) ⊢ A
  τTy l n b (Uⱼ ⊢Γ) = Uⱼ (τCon l n b ⊢Γ) 
  τTy l n b (ℕⱼ ⊢Γ) = ℕⱼ (τCon l n b ⊢Γ)
  τTy l n b (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (τCon l n b ⊢Γ)
  τTy l n b (Emptyⱼ ⊢Γ) = Emptyⱼ (τCon l n b ⊢Γ)
  τTy l n b (Unitⱼ ⊢Γ) = Unitⱼ (τCon l n b ⊢Γ)
  τTy l n b (Πⱼ A ▹ B) = Πⱼ τTy l n b A ▹ τTy l n b B
  τTy l n b (Σⱼ A ▹ B) = Σⱼ τTy l n b A ▹ τTy l n b B
  τTy l n b (univ u) = univ (τTerm l n b u)
  τTy l n b (ϝⱼ g d) = ϝⱼ (TyPerm (addₗ n b (addₗ _ Btrue l)) 0 (τTy _ n b g)) (TyPerm (addₗ n b (addₗ _ Bfalse l)) 0 (τTy _ n b d))
  
  τTerm : ∀ l n b {t}
           → Γ / l ⊢ t ∷ A
           → Γ / (addₗ n b l) ⊢ t ∷ A
  τTerm l n b (ℕⱼ ⊢Γ) = ℕⱼ (τCon l n b ⊢Γ)
  τTerm l n b (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (τCon l n b ⊢Γ)
  τTerm l n b (Emptyⱼ ⊢Γ) = Emptyⱼ (τCon l n b ⊢Γ)
  τTerm l n b (Unitⱼ ⊢Γ) = Unitⱼ (τCon l n b ⊢Γ)
  τTerm l n b (Πⱼ A ▹ B) = Πⱼ τTerm l n b A ▹ τTerm l n b B
  τTerm l n b (Σⱼ A ▹ B) = Σⱼ τTerm l n b A ▹ τTerm l n b B
  τTerm l n b (var ⊢Γ x) = var (τCon l n b ⊢Γ) x
  τTerm l n b (lamⱼ ⊢F x) = lamⱼ (τTy l n b ⊢F) (τTerm l n b x)
  τTerm l n b (t ∘ⱼ u) = τTerm l n b t ∘ⱼ τTerm l n b u
  τTerm l n b (prodⱼ x x₁ x₂ x₃) = prodⱼ (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τTerm l n b (fstⱼ x x₁ x₂) = fstⱼ (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂)
  τTerm l n b (sndⱼ x x₁ x₂) = sndⱼ (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂)
  τTerm l n b (zeroⱼ ⊢Γ) = zeroⱼ (τCon l n b ⊢Γ)
  τTerm l n b (sucⱼ ⊢n) = sucⱼ (τTerm l n b ⊢n)
  τTerm l n b (natrecⱼ x x₁ x₂ x₃) = natrecⱼ (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τTerm l n b (trueⱼ ⊢Γ) = trueⱼ (τCon l n b ⊢Γ)
  τTerm l n b (falseⱼ ⊢Γ) = falseⱼ (τCon l n b ⊢Γ)
  τTerm l n b (boolrecⱼ x x₁ x₂ x₃) = boolrecⱼ (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τTerm l n b (Emptyrecⱼ x x₁) = Emptyrecⱼ (τTy l n b x) (τTerm l n b x₁)
  τTerm l n b (starⱼ ⊢Γ) = starⱼ (τCon l n b ⊢Γ)
  τTerm l n b (conv x x₁) = conv (τTerm l n b x) (τConvTy l n b x₁)
  τTerm l n b (αⱼ x) = αⱼ (τTerm l n b x)
  τTerm l n b (ϝⱼ g d) = ϝⱼ (TermPerm (addₗ n b (addₗ _ Btrue l)) 0 (τTerm _ n b g)) (TermPerm (addₗ n b (addₗ _ Bfalse l)) 0 (τTerm _ n b d))
  
  τConvTy : ∀ l n b {A B}
             → Γ / l ⊢ A ≡ B
             → Γ / addₗ n b l ⊢ A ≡ B
  τConvTy l n b (univ t≡u) = univ (τConvTerm l n b t≡u)
  τConvTy l n b (refl A) = refl (τTy l n b A)
  τConvTy l n b (sym A) = sym (τConvTy l n b A)
  τConvTy l n b (trans t≡u u≡v) = trans (τConvTy l n b t≡u) (τConvTy l n b u≡v)
  τConvTy l n b (Π-cong x x₁ x₂) = Π-cong (τTy l n b x) (τConvTy l n b x₁) (τConvTy l n b x₂)
  τConvTy l n b (Σ-cong x x₁ x₂) = Σ-cong (τTy l n b x) (τConvTy l n b x₁) (τConvTy l n b x₂)
  τConvTy l n b (ϝ-cong g d) = ϝ-cong (ConvTyPerm (addₗ n b (addₗ _ Btrue l)) 0 (τConvTy _ n b g)) (ConvTyPerm (addₗ n b (addₗ _ Bfalse l)) 0 (τConvTy _ n b d))
  
  τConvTerm : ∀ l n b {A t u}
               → Γ / l ⊢ t ≡ u ∷ A
               → Γ / addₗ n b l ⊢ t ≡ u ∷ A
  τConvTerm l n b (refl t) = refl (τTerm l n b t)
  τConvTerm l n b (sym x) = sym (τConvTerm l n b x)
  τConvTerm l n b (trans x x₁) = trans (τConvTerm l n b x) (τConvTerm l n b x₁)
  τConvTerm l n b (conv x x₁) = conv (τConvTerm l n b x) (τConvTy l n b x₁)
  τConvTerm l n b (Π-cong x x₁ x₂) = Π-cong (τTy l n b x) (τConvTerm l n b x₁) (τConvTerm l n b x₂)
  τConvTerm l n b (Σ-cong x x₁ x₂) = Σ-cong (τTy l n b x) (τConvTerm l n b x₁) (τConvTerm l n b x₂)
  τConvTerm l n b (app-cong x x₁) = app-cong (τConvTerm l n b x) (τConvTerm l n b x₁)
  τConvTerm l n b (β-red x x₁ x₂) = β-red (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂)
  τConvTerm l n b (η-eq x x₁ x₂ x₃) = η-eq (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂) (τConvTerm l n b x₃)
  τConvTerm l n b (fst-cong x x₁ x₂) = fst-cong (τTy l n b x) (τTy l n b x₁) (τConvTerm l n b x₂)
  τConvTerm l n b (snd-cong x x₁ x₂) = snd-cong (τTy l n b x) (τTy l n b x₁) (τConvTerm l n b x₂)
  τConvTerm l n b (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τConvTerm l n b (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τConvTerm l n b (Σ-η x x₁ x₂ x₃ x₄ x₅) = Σ-η (τTy l n b x) (τTy l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃) (τConvTerm l n b x₄) (τConvTerm l n b x₅)
  τConvTerm l n b (suc-cong x) = suc-cong (τConvTerm l n b x)
  τConvTerm l n b (natrec-cong x x₁ x₂ x₃) = natrec-cong (τConvTy l n b x) (τConvTerm l n b x₁) (τConvTerm l n b x₂) (τConvTerm l n b x₃)
  τConvTerm l n b (natrec-zero x x₁ x₂) = natrec-zero (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂)
  τConvTerm l n b (natrec-suc x x₁ x₂ x₃) = natrec-suc (τTerm l n b x) (τTy l n b x₁) (τTerm l n b x₂) (τTerm l n b x₃)
  τConvTerm l n b (boolrec-cong x x₁ x₂ x₃) = boolrec-cong (τConvTy l n b x) (τConvTerm l n b x₁) (τConvTerm l n b x₂) (τConvTerm l n b x₃)
  τConvTerm l n b (boolrec-true x x₁ x₂) = boolrec-true (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂)
  τConvTerm l n b (boolrec-false x x₁ x₂) = boolrec-false (τTy l n b x) (τTerm l n b x₁) (τTerm l n b x₂)
  τConvTerm l n b (Emptyrec-cong x x₁) = Emptyrec-cong (τConvTy l n b x) (τConvTerm l n b x₁)
  τConvTerm l n b (η-unit x x₁) = η-unit (τTerm l n b x) (τTerm l n b x₁)
  τConvTerm l n b (α-cong x) = α-cong (τConvTerm l n b x)
  τConvTerm l n b (ϝ-cong g d) = ϝ-cong (ConvTermPerm (addₗ n b (addₗ _ Btrue l)) 0 (τConvTerm _ n b g)) (ConvTermPerm (addₗ n b (addₗ _ Bfalse l)) 0 (τConvTerm _ n b d))
  τConvTerm l n b (α-conv x y) = α-conv (τTerm l n b x) (InThere _ _ _ y _ _)
  

-- Term reduction
data _/_⊢_⇒_∷_ (Γ : Con Term n) : ∀ (l : LCon) → Term n → Term n → Term n → Set where
  conv           : ∀ {l A B t u}
                 → Γ / l ⊢ t ⇒ u ∷ A
                 → Γ / l ⊢ A ≡ B
                 → Γ / l ⊢ t ⇒ u ∷ B
  app-subst      : ∀ {l A B t u a}
                 → Γ / l ⊢ t ⇒ u ∷ Π A ▹ B
                 → Γ / l ⊢ a ∷ A
                 → Γ / l ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  β-red          : ∀ {l A B a t}
                 → Γ / l     ⊢ A
                 → Γ ∙ A / l ⊢ t ∷ B
                 → Γ / l     ⊢ a ∷ A
                 → Γ / l     ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  fst-subst      : ∀ {l t t' F G}
                 → Γ / l ⊢ F
                 → Γ ∙ F / l ⊢ G
                 → Γ / l ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ / l ⊢ fst t ⇒ fst t' ∷ F
  snd-subst      : ∀ {l t t' F G}
                 → Γ / l ⊢ F
                 → Γ ∙ F / l ⊢ G
                 → Γ / l ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ / l ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
  Σ-β₁           : ∀ {l F G t u}
                 → Γ / l ⊢ F
                 → Γ ∙ F / l ⊢ G
                 → Γ / l ⊢ t ∷ F
                 → Γ / l ⊢ u ∷ G [ t ]
                 → Γ / l ⊢ fst (prod t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {l F G t u}
                 → Γ / l ⊢ F
                 → Γ ∙ F / l ⊢ G
                 → Γ / l ⊢ t ∷ F
                 → Γ / l ⊢ u ∷ G [ t ]
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → Γ / l ⊢ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ]
  natrec-subst   : ∀ {l z s n n′ F}
                 → Γ ∙ ℕ / l ⊢ F
                 → Γ / l     ⊢ z ∷ F [ zero ]
                 → Γ / l     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / l     ⊢ n ⇒ n′ ∷ ℕ
                 → Γ / l     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  natrec-zero    : ∀ {l z s F}
                 → Γ ∙ ℕ / l ⊢ F
                 → Γ / l     ⊢ z ∷ F [ zero ]
                 → Γ / l     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / l     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc     : ∀ {l n z s F}
                 → Γ / l     ⊢ n ∷ ℕ
                 → Γ ∙ ℕ / l ⊢ F
                 → Γ / l     ⊢ z ∷ F [ zero ]
                 → Γ / l     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / l     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∷ F [ suc n ]
  boolrec-subst   : ∀ {l t f b b′ F}
                 → Γ ∙ 𝔹 / l ⊢ F
                 → Γ / l     ⊢ t ∷ F [ true ]
                 → Γ / l     ⊢ f ∷ F [ false ]
                 → Γ / l     ⊢ b ⇒ b′ ∷ 𝔹
                 → Γ / l     ⊢ boolrec F t f b ⇒ boolrec F t f b′ ∷ F [ b ]
  boolrec-true    : ∀ {l t f F}
                 → Γ ∙ 𝔹 / l ⊢ F
                 → Γ / l     ⊢ t ∷ F [ true ]
                 → Γ / l     ⊢ f ∷ F [ false ]
                 → Γ / l     ⊢ boolrec F t f true ⇒ t ∷ F [ true ]
  boolrec-false    : ∀ {l t f F}
                 → Γ ∙ 𝔹 / l ⊢ F
                 → Γ / l     ⊢ t ∷ F [ true ]
                 → Γ / l     ⊢ f ∷ F [ false ]
                 → Γ / l     ⊢ boolrec F t f false ⇒ f ∷ F [ false ]
  Emptyrec-subst : ∀ {l n n′ A}
                 → Γ / l     ⊢ A
                 → Γ / l     ⊢ n ⇒ n′ ∷ Empty
                 → Γ / l     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A
  α-subst        : ∀ {l n n' A}
                 → Γ / l     ⊢ A
                 → Γ / l     ⊢ n ⇒ n' ∷ ℕ
                 → Γ / l     ⊢ α n ⇒ α n' ∷ 𝔹
  --α-redtrue      : ∀ {l n}
     --            → Γ / l     ⊢ (natToTerm _ n) ∷ ℕ
   --              → Γ / (addₗ n Btrue l)     ⊢ α (natToTerm _ n) ⇒ (BboolToTerm _ Btrue) ∷ 𝔹
 -- α-redfalse     : ∀ {l n}
      --           → Γ / l     ⊢ (natToTerm _ n) ∷ ℕ
       --          → Γ / (addₗ n Bfalse l)     ⊢ α (natToTerm _ n) ⇒ (BboolToTerm _ Bfalse) ∷ 𝔹
 -- α-trans        : ∀ {l n m t b}
   --              → Γ / l     ⊢ α m ⇒ t ∷ 𝔹
     --            → Γ / (addₗ n b l)     ⊢ α m ⇒ t ∷ 𝔹


-- Type reduction
data _/_⊢_⇒_ (Γ : Con Term n) (l : LCon) : Term n → Term n → Set where
  univ : ∀ {A B}
       → Γ / l ⊢ A ⇒ B ∷ U
       → Γ / l ⊢ A ⇒ B

-- Term reduction closure
data _/_⊢_⇒*_∷_ (Γ : Con Term n) (l : LCon) : Term n → Term n → Term n → Set where
  id  : ∀ {A t}
      → Γ / l ⊢ t ∷ A
      → Γ / l ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ / l ⊢ t  ⇒  t′ ∷ A
      → Γ / l ⊢ t′ ⇒* u  ∷ A
      → Γ / l ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _/_⊢_⇒*_ (Γ : Con Term n) (l : LCon) : Term n → Term n → Set where
  id  : ∀ {A}
      → Γ / l ⊢ A
      → Γ / l ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ / l ⊢ A  ⇒  A′
      → Γ / l ⊢ A′ ⇒* B
      → Γ / l ⊢ A  ⇒* B

-- Type reduction to whnf
_/_⊢_↘_ : (Γ : Con Term n) → (l : LCon)→ Term n → Term n → Set
Γ / l ⊢ A ↘ B = Γ / l ⊢ A ⇒* B × Whnf {l} B

-- Term reduction to whnf
_/_⊢_↘_∷_ : (Γ : Con Term n) → (l : LCon) → Term n → Term n → Term n → Set
Γ / l ⊢ t ↘ u ∷ A = Γ / l ⊢ t ⇒* u ∷ A × Whnf {l} u

-- Type equality with well-formed types
_/_⊢_:≡:_ : (Γ : Con Term n) → (l : LCon) → Term n → Term n → Set
Γ / l ⊢ A :≡: B = Γ / l ⊢ A × Γ / l ⊢ B × (Γ / l ⊢ A ≡ B)

-- Term equality with well-formed terms
_/_⊢_:≡:_∷_ : (Γ : Con Term n) → (l : LCon) → Term n → Term n → Term n → Set
Γ / l ⊢ t :≡: u ∷ A = (Γ / l ⊢ t ∷ A) × (Γ / l ⊢ u ∷ A) × (Γ / l ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _/_⊢_:⇒*:_ (Γ : Con Term n) (l : LCon) (A B : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ / l ⊢ A
    ⊢B : Γ / l ⊢ B
    D  : Γ / l ⊢ A ⇒* B

open _/_⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _/_⊢_:⇒*:_∷_ (Γ : Con Term n) (l : LCon) (t u A : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ / l ⊢ t ∷ A
    ⊢u : Γ / l ⊢ u ∷ A
    d  : Γ / l ⊢ t ⇒* u ∷ A

open _/_⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _/_⊢ˢ_∷_ (Δ : Con Term m) (l : LCon) : (σ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ} → Δ / l ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ / l ⊢ˢ tail σ ∷ Γ
      → Δ / l ⊢  head σ ∷ subst (tail σ) A
      → Δ / l ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _/_⊢ˢ_≡_∷_ (Δ : Con Term m) (l : LCon) : (σ σ′ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ σ′} → Δ / l ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {A σ σ′}
      → Δ / l ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ / l ⊢  head σ ≡ head σ′ ∷ subst (tail σ) A
      → Δ / l ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ_/_▹_ : (W : BindingType) → (l : LCon) → ∀ {F G}
     → Γ / l     ⊢ F
     → Γ ∙ F / l ⊢ G
     → Γ / l     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ ⟧ⱼ l / ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼ l / ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_/_▹_ : (W : BindingType) → (l : LCon) → ∀ {F G}
     → Γ / l     ⊢ F ∷ U
     → Γ ∙ F / l ⊢ G ∷ U
     → Γ / l     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ ⟧ⱼᵤ l / ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼᵤ l / ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
