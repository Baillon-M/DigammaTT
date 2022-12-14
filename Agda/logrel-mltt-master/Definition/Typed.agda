{-# OPTIONS --without-K --safe #-}

module Definition.Typed where

open import Definition.Untyped hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.Sum as TS
import Tools.PropositionalEquality as PE

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
  data ⊢_/_ : Con Term n → {l : LCon} → ⊢ₗ l → Set where
    ε   : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ ε / lε
    _∙_ : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε
          → Γ / lε ⊢ A
          → ⊢ Γ ∙ A / lε
    ϝ   : ∀ {l lε n nε}
          → ⊢ Γ / (⊢ₗ• l lε n Btrue nε)
          → ⊢ Γ / (⊢ₗ• l lε n Bfalse nε)
          → ⊢ Γ / lε
--    τ   : ∀ {l n b}
--          → ⊢ Γ / l
--          → ⊢ Γ / (addₗ n b l)
--     π   : ∀ {l n1 n2 b1 b2}
--           → ⊢ Γ / (addₗ n1 b1 (addₗ n2 b2 l))
--           → ⊢ Γ / (addₗ n2 b2 (addₗ n1 b1 l))
          
  -- Well-formed type
  data _/_⊢_ (Γ : Con Term n) : ∀ {l : LCon} → ⊢ₗ l → Term n → Set where
    Uⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ U
    ℕⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ ℕ
    𝔹ⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ 𝔹
    Emptyⱼ : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Empty
    Unitⱼ  : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Unit
    Πⱼ_▹_  : ∀ {l : LCon} {lε : ⊢ₗ l} → Γ / lε     ⊢ F
           → Γ ∙ F / lε ⊢ G
           → Γ / lε     ⊢ Π F ▹ G
    Σⱼ_▹_  : ∀ {l : LCon} {lε : ⊢ₗ l} → Γ / lε     ⊢ F
           → Γ ∙ F / lε ⊢ G
           → Γ / lε     ⊢ Σ F ▹ G
    univ   : ∀ {l : LCon} {lε : ⊢ₗ l}
           → Γ / lε                        ⊢ A ∷ U
           → Γ / lε                        ⊢ A
    ϝⱼ :     ∀  {l lε F n nε}
           → Γ / (⊢ₗ• l lε n Btrue nε)          ⊢ F
           → Γ / (⊢ₗ• l lε n Bfalse nε)         ⊢ F
           → Γ / lε                        ⊢ F
--    τⱼ   : ∀ {l n b A}
--          → Γ / lε                         ⊢ A
--           → Γ / (addₗ n b lε)               ⊢ A
--     πⱼ   : ∀ {l n1 n2 b1 b2 A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 lε)) ⊢ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 lε)) ⊢ A
          
  -- Well-formed term of a type
  data _/_⊢_∷_ (Γ : Con Term n) : ∀ {l : LCon} → ⊢ₗ l → Term n → Term n → Set where
    Πⱼ_▹_     : ∀ {l : LCon} {lε : ⊢ₗ l} {F G}
              → Γ / lε     ⊢ F ∷ U
              → Γ ∙ F / lε ⊢ G ∷ U
              → Γ / lε     ⊢ Π F ▹ G ∷ U
    Σⱼ_▹_     : ∀ {l : LCon} {lε : ⊢ₗ l} {F G}
              → Γ / lε     ⊢ F ∷ U
              → Γ ∙ F / lε ⊢ G ∷ U
              → Γ / lε     ⊢ Σ F ▹ G ∷ U
    ℕⱼ        : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ ℕ ∷ U
    𝔹ⱼ        : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ 𝔹 ∷ U
    Emptyⱼ    : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Empty ∷ U
    Unitⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Unit ∷ U

    var       : ∀ {l : LCon} {lε : ⊢ₗ l} {A x}
              → ⊢ Γ / lε
              → x ∷ A ∈ Γ
              → Γ / lε ⊢ var x ∷ A

    lamⱼ      : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t}
              → Γ / lε     ⊢ F
              → Γ ∙ F / lε ⊢ t ∷ G
              → Γ / lε     ⊢ lam t ∷ Π F ▹ G
    _∘ⱼ_      : ∀ {l : LCon} {lε : ⊢ₗ l} {g a F G}
              → Γ / lε ⊢     g ∷ Π F ▹ G
              → Γ / lε ⊢     a ∷ F
              → Γ / lε ⊢ g ∘ a ∷ G [ a ]

    prodⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t u}
              → Γ / lε ⊢ F
              → Γ ∙ F / lε ⊢ G
              → Γ / lε ⊢ t ∷ F
              → Γ / lε ⊢ u ∷ G [ t ]
              → Γ / lε ⊢ prod t u ∷ Σ F ▹ G
    fstⱼ      : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t}
              → Γ / lε ⊢ F
              → Γ ∙ F / lε ⊢ G
              → Γ / lε ⊢ t ∷ Σ F ▹ G
              → Γ / lε ⊢ fst t ∷ F
    sndⱼ      : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t}
              → Γ / lε ⊢ F
              → Γ ∙ F / lε ⊢ G
              → Γ / lε ⊢ t ∷ Σ F ▹ G
              → Γ / lε ⊢ snd t ∷ G [ fst t ]

    zeroⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε
              → Γ / lε ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {l : LCon} {lε : ⊢ₗ l} {n}
              → Γ / lε ⊢       n ∷ ℕ
              → Γ / lε ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {l : LCon} {lε : ⊢ₗ l} {G s z n}
              → Γ ∙ ℕ / lε ⊢ G
              → Γ / lε       ⊢ z ∷ G [ zero ]
              → Γ / lε       ⊢ s ∷ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
              → Γ / lε       ⊢ n ∷ ℕ
              → Γ / lε       ⊢ natrec G z s n ∷ G [ n ]

    trueⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε
              → Γ / lε ⊢ true ∷ 𝔹
    falseⱼ    : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε
              → Γ / lε ⊢ false ∷ 𝔹
    boolrecⱼ   : ∀ {l : LCon} {lε : ⊢ₗ l} {G t f b}
              → Γ ∙ 𝔹 / lε ⊢ G
              → Γ / lε       ⊢ t ∷ G [ true ]
              → Γ / lε       ⊢ f ∷ G [ false ]
              → Γ / lε       ⊢ b ∷ 𝔹
              → Γ / lε       ⊢ boolrec G t f b ∷ G [ b ]              
    Emptyrecⱼ : ∀ {l : LCon} {lε : ⊢ₗ l} {A e}
              → Γ / lε ⊢ A → Γ / lε ⊢ e ∷ Empty → Γ / lε ⊢ Emptyrec A e ∷ A

    starⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ star ∷ Unit

    conv      : ∀ {l : LCon} {lε : ⊢ₗ l} {t A B}
              → Γ / lε ⊢ t ∷ A
              → Γ / lε ⊢ A ≡ B
              → Γ / lε ⊢ t ∷ B
    αⱼ  : ∀ {l : LCon} {lε : ⊢ₗ l} {n}
              → Γ / lε ⊢ n ∷ ℕ
              → Γ / lε ⊢ α n ∷ 𝔹
    ϝⱼ :     ∀  {l : LCon} {lε : ⊢ₗ l} {t A n nε}
           → Γ / (⊢ₗ• l lε n Btrue nε)   ⊢ t ∷ A
           → Γ / (⊢ₗ• l lε n Bfalse nε)  ⊢ t ∷ A
           → Γ / lε                 ⊢ t ∷ A
--    τⱼ   : ∀ {l : LCon} {lε n b t A}
--          → Γ / lε                         ⊢ t ∷ A
--          → Γ / (addₗ n b lε)               ⊢ t ∷ A
--     πⱼ   : ∀ {l : LCon} {lε n1 n2 b1 b2 t A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 lε)) ⊢ t ∷ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 lε)) ⊢ t ∷ A

  -- Type equality
  data _/_⊢_≡_ (Γ : Con Term n) : ∀ {l : LCon} → ⊢ₗ l → Term n → Term n → Set where
    univ   : ∀ {l : LCon} {lε : ⊢ₗ l} {A B : Term n}
           → Γ / lε ⊢ A ≡ B ∷ U
           → Γ / lε ⊢ A ≡ B
    refl   : ∀ {l : LCon} {lε : ⊢ₗ l} {A}
           → Γ / lε ⊢ A
           → Γ / lε ⊢ A ≡ A
    sym    : ∀ {l : LCon} {lε : ⊢ₗ l} {A B}
           → Γ / lε ⊢ A ≡ B
           → Γ / lε ⊢ B ≡ A
    trans  : ∀ {l : LCon} {lε : ⊢ₗ l} {A B C}
           → Γ / lε ⊢ A ≡ B
           → Γ / lε ⊢ B ≡ C
           → Γ / lε ⊢ A ≡ C
    Π-cong : ∀ {l : LCon} {lε : ⊢ₗ l} {F H G E}
           → Γ / lε     ⊢ F
           → Γ / lε     ⊢ F ≡ H
           → Γ ∙ F / lε ⊢ G ≡ E
           → Γ / lε     ⊢ Π F ▹ G ≡ Π H ▹ E
    Σ-cong : ∀ {l : LCon} {lε : ⊢ₗ l} {F H G E}
           → Γ / lε     ⊢ F
           → Γ / lε     ⊢ F ≡ H
           → Γ ∙ F / lε ⊢ G ≡ E
           → Γ / lε     ⊢ Σ F ▹ G ≡ Σ H ▹ E
    ϝ-cong : ∀  {l : LCon} {lε : ⊢ₗ l} {F G n nε}
           → Γ / (⊢ₗ• l lε n Btrue nε)   ⊢ F ≡ G
           → Γ / (⊢ₗ• l lε n Bfalse nε)  ⊢ F ≡ G
           → Γ / lε                 ⊢ F ≡ G
--    τⱼ   : ∀ {l n b A B}
--          → Γ / lε                         ⊢ A ≡ B
--          → Γ / (addₗ n b lε)               ⊢ A ≡ B
--     πⱼ   : ∀ {l n1 n2 b1 b2 A B}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 lε)) ⊢ A ≡ B
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 lε)) ⊢ A ≡ B

  -- Term equality
  data _/_⊢_≡_∷_ (Γ : Con Term n) : ∀ {l : LCon} (lε : ⊢ₗ l) → Term n → Term n → Term n → Set where
    refl          : ∀ {l : LCon} {lε : ⊢ₗ l} {t A}
                  → Γ / lε ⊢ t ∷ A
                  → Γ / lε ⊢ t ≡ t ∷ A
    sym           : ∀ {l : LCon} {lε : ⊢ₗ l} {t u A}
                  → Γ / lε ⊢ t ≡ u ∷ A
                  → Γ / lε ⊢ u ≡ t ∷ A
    trans         : ∀ {l : LCon} {lε : ⊢ₗ l} {t u r A}
                  → Γ / lε ⊢ t ≡ u ∷ A
                  → Γ / lε ⊢ u ≡ r ∷ A
                  → Γ / lε ⊢ t ≡ r ∷ A
    conv          : ∀ {l : LCon} {lε : ⊢ₗ l} {A B t u}
                  → Γ / lε ⊢ t ≡ u ∷ A
                  → Γ / lε ⊢ A ≡ B
                  → Γ / lε ⊢ t ≡ u ∷ B
    Π-cong        : ∀ {l : LCon} {lε : ⊢ₗ l} {E F G H}
                  → Γ / lε     ⊢ F
                  → Γ / lε     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F / lε ⊢ G ≡ E       ∷ U
                  → Γ / lε     ⊢ Π F ▹ G ≡ Π H ▹ E ∷ U
    Σ-cong        : ∀ {l : LCon} {lε : ⊢ₗ l} {E F G H}
                  → Γ / lε     ⊢ F
                  → Γ / lε    ⊢ F ≡ H       ∷ U
                  → Γ ∙ F / lε ⊢ G ≡ E       ∷ U
                  → Γ / lε     ⊢ Σ F ▹ G ≡ Σ H ▹ E ∷ U
    app-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {a b f g F G}
                  → Γ / lε ⊢ f ≡ g ∷ Π F ▹ G
                  → Γ / lε ⊢ a ≡ b ∷ F
                  → Γ / lε ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    β-red         : ∀ {l : LCon} {lε : ⊢ₗ l} {a t F G}
                  → Γ / lε     ⊢ F
                  → Γ ∙ F / lε ⊢ t ∷ G
                  → Γ / lε     ⊢ a ∷ F
                  → Γ / lε     ⊢ (lam t) ∘ a ≡ t [ a ] ∷ G [ a ]
    η-eq          : ∀ {l : LCon} {lε : ⊢ₗ l} {f g F G}
                  → Γ / lε     ⊢ F
                  → Γ / lε     ⊢ f ∷ Π F ▹ G
                  → Γ / lε     ⊢ g ∷ Π F ▹ G
                  → Γ ∙ F / lε ⊢ wk1 f ∘ var x0 ≡ wk1 g ∘ var x0 ∷ G
                  → Γ / lε     ⊢ f ≡ g ∷ Π F ▹ G
    fst-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {t t' F G}
                  → Γ / lε ⊢ F
                  → Γ ∙ F / lε ⊢ G
                  → Γ / lε ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ / lε ⊢ fst t ≡ fst t' ∷ F
    snd-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {t t' F G}
                  → Γ / lε ⊢ F
                  → Γ ∙ F / lε ⊢ G
                  → Γ / lε ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ / lε ⊢ snd t ≡ snd t' ∷ G [ fst t ]
    Σ-β₁          : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t u}
                  → Γ / lε ⊢ F
                  → Γ ∙ F / lε ⊢ G
                  → Γ / lε ⊢ t ∷ F
                  → Γ / lε ⊢ u ∷ G [ t ]
                  → Γ / lε ⊢ fst (prod t u) ≡ t ∷ F
    Σ-β₂          : ∀ {l : LCon} {lε : ⊢ₗ l} {F G t u}
                  → Γ / lε ⊢ F
                  → Γ ∙ F / lε ⊢ G
                  → Γ / lε ⊢ t ∷ F
                  → Γ / lε ⊢ u ∷ G [ t ]
                  → Γ / lε ⊢ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]
    Σ-η           : ∀ {l : LCon} {lε : ⊢ₗ l} {p r F G}
                  → Γ / lε ⊢ F
                  → Γ ∙ F / lε ⊢ G
                  → Γ / lε ⊢ p ∷ Σ F ▹ G
                  → Γ / lε ⊢ r ∷ Σ F ▹ G
                  → Γ / lε ⊢ fst p ≡ fst r ∷ F
                  → Γ / lε ⊢ snd p ≡ snd r ∷ G [ fst p ]
                  → Γ / lε ⊢ p ≡ r ∷ Σ F ▹ G
    suc-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {m n}
                  → Γ / lε ⊢ m ≡ n ∷ ℕ
                  → Γ / lε ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {l : LCon} {lε : ⊢ₗ l} {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ / lε ⊢ F ≡ F′
                  → Γ / lε     ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ / lε     ⊢ s ≡ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / lε     ⊢ n ≡ n′ ∷ ℕ
                  → Γ / lε     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {l : LCon} {lε : ⊢ₗ l} {z s F}
                  → Γ ∙ ℕ / lε ⊢ F
                  → Γ / lε     ⊢ z ∷ F [ zero ]
                  → Γ / lε     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / lε     ⊢ natrec F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {l : LCon} {lε : ⊢ₗ l} {n z s F}
                  → Γ / lε     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ / lε ⊢ F
                  → Γ / lε     ⊢ z ∷ F [ zero ]
                  → Γ / lε     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / lε     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                          ∷ F [ suc n ]
    boolrec-cong   : ∀ {l : LCon} {lε : ⊢ₗ l} {t t′ f f′ b b′ F F′}
                  → Γ ∙ 𝔹 / lε ⊢ F ≡ F′
                  → Γ / lε     ⊢ t ≡ t′ ∷ F [ true ]
                  → Γ / lε     ⊢ f ≡ f′ ∷ F [ false ]
                  → Γ / lε     ⊢ b ≡ b′ ∷ 𝔹
                  → Γ / lε     ⊢ boolrec F t f b ≡ boolrec F′ t′ f′ b′ ∷ F [ b ]
    boolrec-true   : ∀ {l : LCon} {lε : ⊢ₗ l} {t f F}
                  → Γ ∙ 𝔹 / lε ⊢ F
                  → Γ / lε     ⊢ t ∷ F [ true ]
                  → Γ / lε     ⊢ f ∷ F [ false ]
                  → Γ / lε     ⊢ boolrec F t f true ≡ t ∷ F [ true ]
    boolrec-false   : ∀ {l : LCon} {lε : ⊢ₗ l} {t f F}
                  → Γ ∙ 𝔹 / lε ⊢ F
                  → Γ / lε     ⊢ t ∷ F [ true ]
                  → Γ / lε     ⊢ f ∷ F [ false ]
                  → Γ / lε     ⊢ boolrec F t f false ≡ f ∷ F [ false ]
    Emptyrec-cong : ∀ {l : LCon} {lε : ⊢ₗ l} {A A' e e'}
                  → Γ / lε ⊢ A ≡ A'
                  → Γ / lε ⊢ e ≡ e' ∷ Empty
                  → Γ / lε ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A
    η-unit        : ∀ {l : LCon} {lε : ⊢ₗ l} {e e'}
                  → Γ / lε ⊢ e ∷ Unit
                  → Γ / lε ⊢ e' ∷ Unit
                  → Γ / lε ⊢ e ≡ e' ∷ Unit
    α-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {m n}
                  → Γ / lε ⊢ m ≡ n ∷ ℕ
                  → Γ / lε ⊢ α m ≡ α n ∷ 𝔹
    ϝ-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {t u n nε}
                  → Γ / (⊢ₗ• l lε n Btrue nε)   ⊢ t ≡ u ∷ A
                  → Γ / (⊢ₗ• l lε n Bfalse nε)  ⊢ t ≡ u ∷ A
                  → Γ / lε                 ⊢ t ≡ u ∷ A
    α-conv      : ∀ {l : LCon} {lε : ⊢ₗ l} {t b}
                   → Γ / lε     ⊢ t ∷ ℕ
                   → (tε : InLCon t b l)
                   → Γ / lε     ⊢ α t ≡ b ∷ 𝔹
--    α-convfalse     : ∀ {l : LCon} {lε n}
--                   → Γ / (addₗ n Bfalse l)      ⊢ (natToTerm _ n) ∷ ℕ
--                   → Γ / (addₗ n Bfalse l)     ⊢ α (natToTerm _ n) ≡ (BboolToTerm _ Bfalse) ∷ 𝔹
--    τⱼ   : ∀ {l : LCon} {lε n b t u A}
--          → Γ / l                         ⊢ t ≡ u ∷ A
--          → Γ / (addₗ n b l)               ⊢ t ≡ u ∷ A
--     πⱼ   : ∀ {l : LCon} {lε n1 n2 b1 b2 t u A}
--           → Γ / (addₗ n1 b1 (addₗ n2 b2 l)) ⊢ t ≡ u ∷ A
--           → Γ / (addₗ n2 b2 (addₗ n1 b1 l)) ⊢ t ≡ u ∷ A




mutual
  ConPerm : ∀ {l : LCon} (lε : ⊢ₗ l) n
           → ⊢ Γ / lε
           → ⊢ Γ / (permutε n lε)
  ConPerm lε n ε = ε
  ConPerm lε n (⊢Γ ∙ ⊢A) = ConPerm lε n  ⊢Γ ∙ TyPerm lε n ⊢A
  ConPerm lε n (ϝ g d) = ϝ (ConPerm _ (1+ n) g) (ConPerm _ (1+ n) d)

  TyPerm : ∀ {l : LCon} (lε : ⊢ₗ l) n
           → Γ / lε ⊢ A
           → Γ / (permutε n lε) ⊢ A
  TyPerm lε n (Uⱼ ⊢Γ) = Uⱼ (ConPerm lε n ⊢Γ) 
  TyPerm lε n (ℕⱼ ⊢Γ) = ℕⱼ (ConPerm lε n ⊢Γ)
  TyPerm lε n (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (ConPerm lε n ⊢Γ)
  TyPerm lε n (Emptyⱼ ⊢Γ) = Emptyⱼ (ConPerm lε n ⊢Γ)
  TyPerm lε n (Unitⱼ ⊢Γ) = Unitⱼ (ConPerm lε n ⊢Γ)
  TyPerm lε n (Πⱼ A ▹ B) = Πⱼ TyPerm lε n A ▹ TyPerm lε n B
  TyPerm lε n (Σⱼ A ▹ B) = Σⱼ TyPerm lε n A ▹ TyPerm lε n B
  TyPerm lε n (univ u) = univ (TermPerm lε n u)
  TyPerm lε n (ϝⱼ g d) = ϝⱼ (TyPerm _ (1+ n) g) (TyPerm _ (1+ n) d)

  TermPerm : ∀ {l : LCon} (lε : ⊢ₗ l) n {t}
           → Γ / lε ⊢ t ∷ A
           → Γ / (permutε n lε) ⊢ t ∷ A
  TermPerm lε n (ℕⱼ ⊢Γ) = ℕⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (Emptyⱼ ⊢Γ) = Emptyⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (Unitⱼ ⊢Γ) = Unitⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (Πⱼ A ▹ B) = Πⱼ TermPerm lε n A ▹ TermPerm lε n B
  TermPerm lε n (Σⱼ A ▹ B) = Σⱼ TermPerm lε n A ▹ TermPerm lε n B
  TermPerm lε n (var ⊢Γ x) = var (ConPerm lε n ⊢Γ) x
  TermPerm lε n (lamⱼ ⊢F x) = lamⱼ (TyPerm lε n ⊢F) (TermPerm lε n x)
  TermPerm lε n (t ∘ⱼ u) = TermPerm lε n t ∘ⱼ TermPerm lε n u
  TermPerm lε n (prodⱼ x x₁ x₂ x₃) = prodⱼ (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  TermPerm lε n (fstⱼ x x₁ x₂) = fstⱼ (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂)
  TermPerm lε n (sndⱼ x x₁ x₂) = sndⱼ (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂)
  TermPerm lε n (zeroⱼ ⊢Γ) = zeroⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (sucⱼ ⊢n) = sucⱼ (TermPerm lε n ⊢n)
  TermPerm lε n (natrecⱼ x x₁ x₂ x₃) = natrecⱼ (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  TermPerm lε n (trueⱼ ⊢Γ) = trueⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (falseⱼ ⊢Γ) = falseⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (boolrecⱼ x x₁ x₂ x₃) = boolrecⱼ (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  TermPerm lε n (Emptyrecⱼ x x₁) = Emptyrecⱼ (TyPerm lε n x) (TermPerm lε n x₁)
  TermPerm lε n (starⱼ ⊢Γ) = starⱼ (ConPerm lε n ⊢Γ)
  TermPerm lε n (conv x x₁) = conv (TermPerm lε n x) (ConvTyPerm lε n x₁)
  TermPerm lε n (αⱼ x) = αⱼ (TermPerm lε n x)
  TermPerm lε n (ϝⱼ g d) = ϝⱼ (TermPerm _ (1+ n) g) (TermPerm _ (1+ n) d)

  ConvTyPerm : ∀ {l : LCon} (lε : ⊢ₗ l) n {A B}
             → Γ / lε ⊢ A ≡ B
             → Γ / (permutε n lε) ⊢ A ≡ B
  ConvTyPerm lε n (univ t≡u) = univ (ConvTermPerm lε n t≡u)
  ConvTyPerm lε n (refl A) = refl (TyPerm lε n A)
  ConvTyPerm lε n (sym A) = sym (ConvTyPerm lε n A)
  ConvTyPerm lε n (trans t≡u u≡v) = trans (ConvTyPerm lε n t≡u) (ConvTyPerm lε n u≡v)
  ConvTyPerm lε n (Π-cong x x₁ x₂) = Π-cong (TyPerm lε n x) (ConvTyPerm lε n x₁) (ConvTyPerm lε n x₂)
  ConvTyPerm lε n (Σ-cong x x₁ x₂) = Σ-cong (TyPerm lε n x) (ConvTyPerm lε n x₁) (ConvTyPerm lε n x₂)
  ConvTyPerm lε n (ϝ-cong g d) = ϝ-cong (ConvTyPerm _ (1+ n) g) (ConvTyPerm _ (1+ n) d)

  ConvTermPerm : ∀ {l : LCon} (lε : ⊢ₗ l) n {A t u}
               → Γ / lε ⊢ t ≡ u ∷ A
               → Γ / (permutε n lε) ⊢ t ≡ u ∷ A
  ConvTermPerm lε n (refl t) = refl (TermPerm lε n t)
  ConvTermPerm lε n (sym x) = sym (ConvTermPerm lε n x)
  ConvTermPerm lε n (trans x x₁) = trans (ConvTermPerm lε n x) (ConvTermPerm lε n x₁)
  ConvTermPerm lε n (conv x x₁) = conv (ConvTermPerm lε n x) (ConvTyPerm lε n x₁)
  ConvTermPerm lε n (Π-cong x x₁ x₂) = Π-cong (TyPerm lε n x) (ConvTermPerm lε n x₁) (ConvTermPerm lε n x₂)
  ConvTermPerm lε n (Σ-cong x x₁ x₂) = Σ-cong (TyPerm lε n x) (ConvTermPerm lε n x₁) (ConvTermPerm lε n x₂)
  ConvTermPerm lε n (app-cong x x₁) = app-cong (ConvTermPerm lε n x) (ConvTermPerm lε n x₁)
  ConvTermPerm lε n (β-red x x₁ x₂) = β-red (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂)
  ConvTermPerm lε n (η-eq x x₁ x₂ x₃) = η-eq (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂) (ConvTermPerm lε n x₃)
  ConvTermPerm lε n (fst-cong x x₁ x₂) = fst-cong (TyPerm lε n x) (TyPerm lε n x₁) (ConvTermPerm lε n x₂)
  ConvTermPerm lε n (snd-cong x x₁ x₂) = snd-cong (TyPerm lε n x) (TyPerm lε n x₁) (ConvTermPerm lε n x₂)
  ConvTermPerm lε n (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  ConvTermPerm lε n (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  ConvTermPerm lε n (Σ-η x x₁ x₂ x₃ x₄ x₅) = Σ-η (TyPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃) (ConvTermPerm lε n x₄) (ConvTermPerm lε n x₅)
  ConvTermPerm lε n (suc-cong x) = suc-cong (ConvTermPerm lε n x)
  ConvTermPerm lε n (natrec-cong x x₁ x₂ x₃) = natrec-cong (ConvTyPerm lε n x) (ConvTermPerm lε n x₁) (ConvTermPerm lε n x₂) (ConvTermPerm lε n x₃)
  ConvTermPerm lε n (natrec-zero x x₁ x₂) = natrec-zero (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂)
  ConvTermPerm lε n (natrec-suc x x₁ x₂ x₃) = natrec-suc (TermPerm lε n x) (TyPerm lε n x₁) (TermPerm lε n x₂) (TermPerm lε n x₃)
  ConvTermPerm lε n (boolrec-cong x x₁ x₂ x₃) = boolrec-cong (ConvTyPerm lε n x) (ConvTermPerm lε n x₁) (ConvTermPerm lε n x₂) (ConvTermPerm lε n x₃)
  ConvTermPerm lε n (boolrec-true x x₁ x₂) = boolrec-true (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂)
  ConvTermPerm lε n (boolrec-false x x₁ x₂) = boolrec-false (TyPerm lε n x) (TermPerm lε n x₁) (TermPerm lε n x₂)
  ConvTermPerm lε n (Emptyrec-cong x x₁) = Emptyrec-cong (ConvTyPerm lε n x) (ConvTermPerm lε n x₁)
  ConvTermPerm lε n (η-unit x x₁) = η-unit (TermPerm lε n x) (TermPerm lε n x₁)
  ConvTermPerm lε n (α-cong x) = α-cong (ConvTermPerm lε n x)
  ConvTermPerm lε n (ϝ-cong g d) = ϝ-cong (ConvTermPerm _ (1+ n) g) (ConvTermPerm _ (1+ n) d)
  ConvTermPerm (⊢ₗ• l lε m b mbε) 0 (α-conv x (InHere t b t=m u=b εₗ)) = α-conv (TermPerm _ 0 x) (InHere _ b t=m u=b εₗ)  
  ConvTermPerm (⊢ₗ• _ (⊢ₗ• l lε t2 b2 tbε2) t b tbε) 0 (α-conv x (InHere t1 b1 t=m u=b _)) = α-conv (TermPerm _ 0 x) (InThere _ (InHere _ _ t=m u=b _) t2 b2)
  ConvTermPerm _ 0 (α-conv x (InThere .(addₗ t b l) (InHere t b t=m u=b l) _ _)) = α-conv (TermPerm _ 0 x) (InHere _ _ t=m u=b _)
  ConvTermPerm (⊢ₗ• _ (⊢ₗ• l lε t2 b2 tbε2) t b tbε) 0 (α-conv x (InThere .(addₗ _ _ l) (InThere .l x₄ _ _) _ _)) = α-conv (TermPerm _ 0 x) (InThere _ (InThere  _ x₄ _ _) _ _)
  ConvTermPerm (⊢ₗ• εₗ ⊢ₗₑ t2 b2 tbε2) (1+ n) (α-conv x (InHere t b t=m u=b _)) = α-conv (TermPerm _ (1+ n) x) (InHere _ _ t=m u=b _)
  ConvTermPerm (⊢ₗ• l lε t2 b2 tbε2) (1+ n) (α-conv x (InThere .l x₂ _ _)) = α-conv (TermPerm _ (1+ n) x) (InThere _ (permutInLCon _ _ _ _ x₂) _ _)
  ConvTermPerm (⊢ₗ• _ (⊢ₗ• l lε t2 b2 tbε2) t b1 tbε) (1+ n) (α-conv x (InHere _ _ t=m u=b _)) = α-conv (TermPerm _ (1+ n) x) (InHere _ b1  t=m u=b _)


NatToℕ : ∀ m {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ (natToTerm _ m) ∷ ℕ
NatToℕ 0 ⊢Γ = zeroⱼ ⊢Γ
NatToℕ (1+ m) ⊢Γ = sucⱼ (NatToℕ m ⊢Γ)



mutual
  τCon : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε
           → ⊢ Γ / lε
           → ⊢ Γ / (⊢ₗ• l lε n b nbε)
  τCon lε n b nbε ε = ε
  τCon lε n b nbε (⊢Γ ∙ ⊢A) = τCon lε n b nbε ⊢Γ ∙ τTy lε n b nbε ⊢A
  τCon lε m b nbε (ϝ {n = n} g d) with decidEqNat m n
  τCon lε m Btrue nbε (ϝ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε  = g
  τCon lε m Bfalse nbε (ϝ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = d
  τCon lε m b nbε (ϝ {n = n} {nε = nε} g d) | TS.inj₂ neq = ϝ (ConPerm _ 0 (τCon _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) g))
                                                             (ConPerm _ 0 (τCon _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) d))
  -- = ϝ (ConPerm {!!} 0 (τCon (⊢ₗ• _ _ _ Btrue _) _ _ {!!} g)) (ConPerm {!!} {!!} {!!})

  τTy : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε
           → Γ / lε ⊢ A
           → Γ / (⊢ₗ• l lε n b nbε) ⊢ A
  τTy lε n b nbε (Uⱼ ⊢Γ) = Uⱼ (τCon lε n b nbε ⊢Γ) 
  τTy lε n b nbε (ℕⱼ ⊢Γ) = ℕⱼ (τCon lε n b nbε ⊢Γ)
  τTy lε n b nbε (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (τCon lε n b nbε ⊢Γ)
  τTy lε n b nbε (Emptyⱼ ⊢Γ) = Emptyⱼ (τCon lε n b nbε ⊢Γ)
  τTy lε n b nbε (Unitⱼ ⊢Γ) = Unitⱼ (τCon lε n b nbε ⊢Γ)
  τTy lε n b nbε (Πⱼ A ▹ B) = Πⱼ τTy lε n b nbε A ▹ τTy lε n b nbε B
  τTy lε n b nbε (Σⱼ A ▹ B) = Σⱼ τTy lε n b nbε A ▹ τTy lε n b nbε B
  τTy lε n b nbε (univ u) = univ (τTerm lε n b nbε u)
  τTy lε m b nbε (ϝⱼ {n = n} {nε = nε} g d) with decidEqNat m n
  τTy lε m Btrue nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = g
  τTy lε m Bfalse nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = d
  τTy lε m b nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₂ neq  = ϝⱼ (TyPerm _ 0 (τTy _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) g))
                                                               (TyPerm _ 0 (τTy _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) d))
  
  τTerm : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {t}
           → Γ / lε ⊢ t ∷ A
           → Γ / (⊢ₗ• l lε n b nbε) ⊢ t ∷ A
  τTerm lε n b nbε (ℕⱼ ⊢Γ) = ℕⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (Emptyⱼ ⊢Γ) = Emptyⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (Unitⱼ ⊢Γ) = Unitⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (Πⱼ A ▹ B) = Πⱼ τTerm lε n b nbε A ▹ τTerm lε n b nbε B
  τTerm lε n b nbε (Σⱼ A ▹ B) = Σⱼ τTerm lε n b nbε A ▹ τTerm lε n b nbε B
  τTerm lε n b nbε (var ⊢Γ x) = var (τCon lε n b nbε ⊢Γ) x
  τTerm lε n b nbε (lamⱼ ⊢F x) = lamⱼ (τTy lε n b nbε ⊢F) (τTerm lε n b nbε x)
  τTerm lε n b nbε (t ∘ⱼ u) = τTerm lε n b nbε t ∘ⱼ τTerm lε n b nbε u
  τTerm lε n b nbε (prodⱼ x x₁ x₂ x₃) = prodⱼ (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τTerm lε n b nbε (fstⱼ x x₁ x₂) = fstⱼ (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τTerm lε n b nbε (sndⱼ x x₁ x₂) = sndⱼ (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τTerm lε n b nbε (zeroⱼ ⊢Γ) = zeroⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (sucⱼ ⊢n) = sucⱼ (τTerm lε n b nbε ⊢n)
  τTerm lε n b nbε (natrecⱼ x x₁ x₂ x₃) = natrecⱼ (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τTerm lε n b nbε (trueⱼ ⊢Γ) = trueⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (falseⱼ ⊢Γ) = falseⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (boolrecⱼ x x₁ x₂ x₃) = boolrecⱼ (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τTerm lε n b nbε (Emptyrecⱼ x x₁) = Emptyrecⱼ (τTy lε n b nbε x) (τTerm lε n b nbε x₁)
  τTerm lε n b nbε (starⱼ ⊢Γ) = starⱼ (τCon lε n b nbε ⊢Γ)
  τTerm lε n b nbε (conv x x₁) = conv (τTerm lε n b nbε x) (τConvTy lε n b nbε x₁)
  τTerm lε n b nbε (αⱼ x) = αⱼ (τTerm lε n b nbε x)
  τTerm lε m b nbε (ϝⱼ {n = n} {nε = nε} g d) with decidEqNat m n
  τTerm lε m Btrue nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = g
  τTerm lε m Bfalse nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = d
  τTerm lε m b nbε (ϝⱼ {n = n} {nε = nε} g d) | TS.inj₂ neq  = ϝⱼ (TermPerm _ 0 (τTerm _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) g))
                                                                (TermPerm _ 0 (τTerm _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) d))
  
  τConvTy : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {A B}
             → Γ / lε ⊢ A ≡ B
             → Γ / (⊢ₗ• l lε n b nbε) ⊢ A ≡ B
  τConvTy lε n b nbε (univ t≡u) = univ (τConvTerm lε n b nbε t≡u)
  τConvTy lε n b nbε (refl A) = refl (τTy lε n b nbε A)
  τConvTy lε n b nbε (sym A) = sym (τConvTy lε n b nbε A)
  τConvTy lε n b nbε (trans t≡u u≡v) = trans (τConvTy lε n b nbε t≡u) (τConvTy lε n b nbε u≡v)
  τConvTy lε n b nbε (Π-cong x x₁ x₂) = Π-cong (τTy lε n b nbε x) (τConvTy lε n b nbε x₁) (τConvTy lε n b nbε x₂)
  τConvTy lε n b nbε (Σ-cong x x₁ x₂) = Σ-cong (τTy lε n b nbε x) (τConvTy lε n b nbε x₁) (τConvTy lε n b nbε x₂)
  τConvTy lε m b nbε (ϝ-cong {n = n} {nε = nε} g d) with decidEqNat m n
  τConvTy lε m Btrue nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = g
  τConvTy lε m Bfalse nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = d
  τConvTy lε m b nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₂ neq  = ϝ-cong (ConvTyPerm _ 0 (τConvTy _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) g))
                                                                           (ConvTyPerm _ 0 (τConvTy _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) d))
  
  τConvTerm : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {A t u}
               → Γ / lε ⊢ t ≡ u ∷ A
               → Γ / (⊢ₗ• l lε n b nbε) ⊢ t ≡ u ∷ A
  τConvTerm lε n b nbε (refl t) = refl (τTerm lε n b nbε t)
  τConvTerm lε n b nbε (sym x) = sym (τConvTerm lε n b nbε x)
  τConvTerm lε n b nbε (trans x x₁) = trans (τConvTerm lε n b nbε x) (τConvTerm lε n b nbε x₁)
  τConvTerm lε n b nbε (conv x x₁) = conv (τConvTerm lε n b nbε x) (τConvTy lε n b nbε x₁)
  τConvTerm lε n b nbε (Π-cong x x₁ x₂) = Π-cong (τTy lε n b nbε x) (τConvTerm lε n b nbε x₁) (τConvTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (Σ-cong x x₁ x₂) = Σ-cong (τTy lε n b nbε x) (τConvTerm lε n b nbε x₁) (τConvTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (app-cong x x₁) = app-cong (τConvTerm lε n b nbε x) (τConvTerm lε n b nbε x₁)
  τConvTerm lε n b nbε (β-red x x₁ x₂) = β-red (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (η-eq x x₁ x₂ x₃) = η-eq (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂) (τConvTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (fst-cong x x₁ x₂) = fst-cong (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τConvTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (snd-cong x x₁ x₂) = snd-cong (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τConvTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (Σ-η x x₁ x₂ x₃ x₄ x₅) = Σ-η (τTy lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃) (τConvTerm lε n b nbε x₄) (τConvTerm lε n b nbε x₅)
  τConvTerm lε n b nbε (suc-cong x) = suc-cong (τConvTerm lε n b nbε x)
  τConvTerm lε n b nbε (natrec-cong x x₁ x₂ x₃) = natrec-cong (τConvTy lε n b nbε x) (τConvTerm lε n b nbε x₁) (τConvTerm lε n b nbε x₂) (τConvTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (natrec-zero x x₁ x₂) = natrec-zero (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (natrec-suc x x₁ x₂ x₃) = natrec-suc (τTerm lε n b nbε x) (τTy lε n b nbε x₁) (τTerm lε n b nbε x₂) (τTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (boolrec-cong x x₁ x₂ x₃) = boolrec-cong (τConvTy lε n b nbε x) (τConvTerm lε n b nbε x₁) (τConvTerm lε n b nbε x₂) (τConvTerm lε n b nbε x₃)
  τConvTerm lε n b nbε (boolrec-true x x₁ x₂) = boolrec-true (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (boolrec-false x x₁ x₂) = boolrec-false (τTy lε n b nbε x) (τTerm lε n b nbε x₁) (τTerm lε n b nbε x₂)
  τConvTerm lε n b nbε (Emptyrec-cong x x₁) = Emptyrec-cong (τConvTy lε n b nbε x) (τConvTerm lε n b nbε x₁)
  τConvTerm lε n b nbε (η-unit x x₁) = η-unit (τTerm lε n b nbε x) (τTerm lε n b nbε x₁)
  τConvTerm lε n b nbε (α-cong x) = α-cong (τConvTerm lε n b nbε x)
  τConvTerm lε m b nbε (ϝ-cong {n = n} {nε = nε} g d) with decidEqNat m n
  τConvTerm lε m Btrue nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = g
  τConvTerm lε m Bfalse nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ e rewrite e rewrite NotInLConNatHProp _ _ nε nbε = d
  τConvTerm lε m b nbε (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₂ neq  = ϝ-cong (ConvTermPerm _ 0 (τConvTerm _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) g))
                                                                             (ConvTermPerm _ 0 (τConvTerm _ m b (NotInThereNat _ nbε _ _ (DifferentDifferentNat m n neq)) d))
  τConvTerm lε n b nbε (α-conv x y) = α-conv (τTerm lε n b nbε x) (InThere _ y _ _)


-- -- ConvU : ∀ lε → Γ / lε ⊢ A ≡ U
-- --             → A PE.≡ U
-- -- ConvU lε (reflε ⊢Γ) = PE.refl
-- -- ConvU lε (univ x) = {!!}
-- -- ConvU lε (sym x) = {!!}
-- -- ConvU lε (trans x x₁) = {!!}
-- -- ConvU lε (ϝ-cong x x₁) = {!!}

-- mutual
--   τCon-rev : ∀ lε n b
--            → ⊢ Γ / (addₗ n b l)
--            → ⊢ Γ / l
--   τCon-rev lε n b ε = ε
--   τCon-rev lε n b (⊢Γ ∙ ⊢A) = τCon-rev lε n b ⊢Γ ∙ τTy-rev lε n b ⊢A
--   τCon-rev lε n b (ϝ g d) = ϝ {!!} {!!}

--   τTy-rev : ∀ lε n b
--            → Γ / (addₗ n b l) ⊢ A
--            → Γ / lε ⊢ A
--   τTy-rev lε n b (Uⱼ ⊢Γ) = Uⱼ (τCon-rev lε n b ⊢Γ) 
--   τTy-rev lε n b (ℕⱼ ⊢Γ) = ℕⱼ (τCon-rev lε n b ⊢Γ)
--   τTy-rev lε n b (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (τCon-rev lε n b ⊢Γ)
--   τTy-rev lε n b (Emptyⱼ ⊢Γ) = Emptyⱼ (τCon-rev lε n b ⊢Γ)
--   τTy-rev lε n b (Unitⱼ ⊢Γ) = Unitⱼ (τCon-rev lε n b ⊢Γ)
--   τTy-rev lε n b (Πⱼ A ▹ B) = Πⱼ τTy-rev lε n b A ▹ τTy-rev lε n b B
--   τTy-rev lε n b (Σⱼ A ▹ B) = Σⱼ τTy-rev lε n b A ▹ τTy-rev lε n b B
--   τTy-rev lε n b (univ u) = {!!}
--   τTy-rev lε n b (ϝⱼ g d) = ϝⱼ {!!} {!!}
  

-- Term reduction
data _/_⊢_⇒_∷_ (Γ : Con Term n) : ∀ {l : LCon} (lε : ⊢ₗ l) → Term n → Term n → Term n → Set where
  conv           : ∀ {l : LCon} {lε : ⊢ₗ l} {A B t u}
                 → Γ / lε ⊢ t ⇒ u ∷ A
                 → Γ / lε ⊢ A ≡ B
                 → Γ / lε ⊢ t ⇒ u ∷ B
  app-subst      : ∀ {l : LCon} {lε : ⊢ₗ l} {A B t u a}
                 → Γ / lε ⊢ t ⇒ u ∷ Π A ▹ B
                 → Γ / lε ⊢ a ∷ A
                 → Γ / lε ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  β-red          : ∀ {l : LCon} {lε : ⊢ₗ l} {  A B a t}
                 → Γ / lε     ⊢ A
                 → Γ ∙ A / lε ⊢ t ∷ B
                 → Γ / lε     ⊢ a ∷ A
                 → Γ / lε     ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  fst-subst      : ∀ {l : LCon} {lε : ⊢ₗ l} {  t t' F G}
                 → Γ / lε ⊢ F
                 → Γ ∙ F / lε ⊢ G
                 → Γ / lε ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ / lε ⊢ fst t ⇒ fst t' ∷ F
  snd-subst      : ∀ {l : LCon} {lε : ⊢ₗ l} {  t t' F G}
                 → Γ / lε ⊢ F
                 → Γ ∙ F / lε ⊢ G
                 → Γ / lε ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ / lε ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
  Σ-β₁           : ∀ {l : LCon} {lε : ⊢ₗ l} {  F G t u}
                 → Γ / lε ⊢ F
                 → Γ ∙ F / lε ⊢ G
                 → Γ / lε ⊢ t ∷ F
                 → Γ / lε ⊢ u ∷ G [ t ]
                 → Γ / lε ⊢ fst (prod t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {l : LCon} {lε : ⊢ₗ l} {  F G t u}
                 → Γ / lε ⊢ F
                 → Γ ∙ F / lε ⊢ G
                 → Γ / lε ⊢ t ∷ F
                 → Γ / lε ⊢ u ∷ G [ t ]
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → Γ / lε ⊢ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ]
  natrec-subst   : ∀ {l : LCon} {lε : ⊢ₗ l} {  z s n n′ F}
                 → Γ ∙ ℕ / lε ⊢ F
                 → Γ / lε     ⊢ z ∷ F [ zero ]
                 → Γ / lε     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / lε     ⊢ n ⇒ n′ ∷ ℕ
                 → Γ / lε     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  natrec-zero    : ∀ {l : LCon} {lε : ⊢ₗ l} {  z s F}
                 → Γ ∙ ℕ / lε ⊢ F
                 → Γ / lε     ⊢ z ∷ F [ zero ]
                 → Γ / lε     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / lε     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc     : ∀ {l : LCon} {lε : ⊢ₗ l} {  n z s F}
                 → Γ / lε     ⊢ n ∷ ℕ
                 → Γ ∙ ℕ / lε ⊢ F
                 → Γ / lε     ⊢ z ∷ F [ zero ]
                 → Γ / lε     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ / lε     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∷ F [ suc n ]
  boolrec-subst   : ∀ {l : LCon} {lε : ⊢ₗ l} {  t f b b′ F}
                 → Γ ∙ 𝔹 / lε ⊢ F
                 → Γ / lε     ⊢ t ∷ F [ true ]
                 → Γ / lε     ⊢ f ∷ F [ false ]
                 → Γ / lε     ⊢ b ⇒ b′ ∷ 𝔹
                 → Γ / lε     ⊢ boolrec F t f b ⇒ boolrec F t f b′ ∷ F [ b ]
  boolrec-true    : ∀ {l : LCon} {lε : ⊢ₗ l} {  t f F}
                 → Γ ∙ 𝔹 / lε ⊢ F
                 → Γ / lε     ⊢ t ∷ F [ true ]
                 → Γ / lε     ⊢ f ∷ F [ false ]
                 → Γ / lε     ⊢ boolrec F t f true ⇒ t ∷ F [ true ]
  boolrec-false    : ∀ {l : LCon} {lε : ⊢ₗ l} {  t f F}
                 → Γ ∙ 𝔹 / lε ⊢ F
                 → Γ / lε     ⊢ t ∷ F [ true ]
                 → Γ / lε     ⊢ f ∷ F [ false ]
                 → Γ / lε     ⊢ boolrec F t f false ⇒ f ∷ F [ false ]
  Emptyrec-subst : ∀ {l : LCon} {lε : ⊢ₗ l} {  n n′ A}
                 → Γ / lε     ⊢ A
                 → Γ / lε     ⊢ n ⇒ n′ ∷ Empty
                 → Γ / lε     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A
  α-subst        : ∀ {l : LCon} {lε : ⊢ₗ l} {  n n'}
                 → Γ / lε     ⊢ n ⇒ n' ∷ ℕ
                 → Γ / lε     ⊢ α n ⇒ α n' ∷ 𝔹
  α-red          : ∀ {l : LCon} {lε : ⊢ₗ l} {n b}
                 → Γ / lε     ⊢ n ∷ ℕ
                 → InLCon n b l
                 → Γ / lε     ⊢ α n ⇒ b ∷ 𝔹


τRedTerm : ∀ {l : LCon} {lε : ⊢ₗ l} {t u A n b nε}
             → Γ / lε ⊢ t ⇒ u ∷ A
             → Γ / (⊢ₗ• l lε n b nε) ⊢ t ⇒ u ∷ A
τRedTerm (conv x x₁) = conv (τRedTerm x) (τConvTy _ _ _ _ x₁)
τRedTerm (app-subst x x₁) = app-subst (τRedTerm x) (τTerm _ _ _ _ x₁)
τRedTerm (β-red x x₁ x₂) = β-red (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂)
τRedTerm (fst-subst x x₁ x₂) = fst-subst (τTy _ _ _ _ x) (τTy _ _ _ _ x₁) (τRedTerm x₂)
τRedTerm (snd-subst x x₁ x₂) = snd-subst (τTy _ _ _ _ x) (τTy _ _ _ _ x₁) (τRedTerm x₂)
τRedTerm (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (τTy _ _ _ _ x) (τTy _ _ _ _ x₁) (τTerm _ _ _ _ x₂) (τTerm _ _ _ _ x₃)
τRedTerm (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (τTy _ _ _ _ x) (τTy _ _ _ _ x₁) (τTerm _ _ _ _ x₂) (τTerm _ _ _ _ x₃)
τRedTerm (natrec-subst x x₁ x₂ x₃) = natrec-subst (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂) (τRedTerm x₃)
τRedTerm (natrec-zero x x₁ x₂) = natrec-zero (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂)
τRedTerm (natrec-suc x x₁ x₂ x₃) = natrec-suc (τTerm _ _ _ _ x) (τTy _ _ _ _ x₁) (τTerm _ _ _ _ x₂) (τTerm _ _ _ _ x₃)
τRedTerm (boolrec-subst x x₁ x₂ x₃) = boolrec-subst (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂) (τRedTerm x₃)
τRedTerm (boolrec-true x x₁ x₂) = boolrec-true (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂)
τRedTerm (boolrec-false x x₁ x₂) = boolrec-false (τTy _ _ _ _ x) (τTerm _ _ _ _ x₁) (τTerm _ _ _ _ x₂)
τRedTerm (Emptyrec-subst x x₁) = Emptyrec-subst (τTy _ _ _ _ x) (τRedTerm x₁)
τRedTerm (α-subst x₁) = α-subst (τRedTerm x₁)
τRedTerm (α-red ⊢n inl) = α-red (τTerm _ _ _ _ ⊢n) (InThere _ inl _ _)


τRedTerm≤ₗ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t u A}
             → l ≤ₗ l'
             → Γ / lε ⊢ t ⇒ u ∷ A
             → Γ / lε' ⊢ t ⇒ u ∷ A
τRedTerm≤ₗ {lε = lε} {lε' = lε'} ≤ₗ-refl t⇒u rewrite ⊢ₗ-HProp _ lε lε' = t⇒u
τRedTerm≤ₗ {lε = lε} {lε' =  ⊢ₗ• l lε' n b nε} (≤ₗ-add n b l' ≤ε) t⇒u =  τRedTerm (τRedTerm≤ₗ ≤ε t⇒u)



-- Type reduction
data _/_⊢_⇒_ (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) : Term n → Term n → Set where
  univ : ∀ {A B}
       → Γ / lε ⊢ A ⇒ B ∷ U
       → Γ / lε ⊢ A ⇒ B

-- Term reduction closure
data _/_⊢_⇒*_∷_ (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) : Term n → Term n → Term n → Set where
  id  : ∀ {A t}
      → Γ / lε ⊢ t ∷ A
      → Γ / lε ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ / lε ⊢ t  ⇒  t′ ∷ A
      → Γ / lε ⊢ t′ ⇒* u  ∷ A
      → Γ / lε ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _/_⊢_⇒*_ (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) : Term n → Term n → Set where
  id  : ∀ {A}
      → Γ / lε ⊢ A
      → Γ / lε ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ / lε ⊢ A  ⇒  A′
      → Γ / lε ⊢ A′ ⇒* B
      → Γ / lε ⊢ A  ⇒* B

-- Type reduction to whnf
_/_⊢_↘_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Set
Γ / lε ⊢ A ↘ B = Γ / lε ⊢ A ⇒* B × Whnf {_} {lε} B

-- Term reduction to whnf
_/_⊢_↘_∷_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Term n → Set
Γ / lε ⊢ t ↘ u ∷ A = Γ / lε ⊢ t ⇒* u ∷ A × Whnf {_} {lε} u

-- Type equality with well-formed types
_/_⊢_:≡:_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Set
Γ / lε ⊢ A :≡: B = Γ / lε ⊢ A × Γ / lε ⊢ B × (Γ / lε ⊢ A ≡ B)

-- Term equality with well-formed terms
_/_⊢_:≡:_∷_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Term n → Set
Γ / lε ⊢ t :≡: u ∷ A = (Γ / lε ⊢ t ∷ A) × (Γ / lε ⊢ u ∷ A) × (Γ / lε ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _/_⊢_:⇒*:_ (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (A B : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ / lε ⊢ A
    ⊢B : Γ / lε ⊢ B
    D  : Γ / lε ⊢ A ⇒* B

open _/_⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _/_⊢_:⇒*:_∷_ (Γ : Con Term n) {l : LCon} (lε : ⊢ₗ l) (t u A : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ / lε ⊢ t ∷ A
    ⊢u : Γ / lε ⊢ u ∷ A
    d  : Γ / lε ⊢ t ⇒* u ∷ A

open _/_⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _/_⊢ˢ_∷_ (Δ : Con Term m) {l : LCon} (lε : ⊢ₗ l) : (σ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ} → Δ / lε ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ / lε ⊢ˢ tail σ ∷ Γ
      → Δ / lε ⊢  head σ ∷ subst (tail σ) A
      → Δ / lε ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _/_⊢ˢ_≡_∷_ (Δ : Con Term m) {l : LCon} (lε : ⊢ₗ l) : (σ σ′ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ σ′} → Δ / lε ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {A σ σ′}
      → Δ / lε ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ / lε ⊢  head σ ≡ head σ′ ∷ subst (tail σ) A
      → Δ / lε ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamentalε theorem for substitutions.

⟦_⟧ⱼ_/_▹_ : (W : BindingType) → {l : LCon} → (lε : ⊢ₗ l) → ∀ {F G}
     → Γ / lε     ⊢ F
     → Γ ∙ F / lε ⊢ G
     → Γ / lε     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ ⟧ⱼ lε / ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼ lε / ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_/_▹_ : (W : BindingType) → {l : LCon} → (lε : ⊢ₗ l) → ∀ {F G}
     → Γ / lε     ⊢ F ∷ U
     → Γ ∙ F / lε ⊢ G ∷ U
     → Γ / lε     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ ⟧ⱼᵤ lε / ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼᵤ lε / ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
