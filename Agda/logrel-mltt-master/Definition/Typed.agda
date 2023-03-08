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
--    ϝ   : ∀ {l lε n nε}
--          → ⊢ Γ / (⊢ₗ• l lε n Btrue nε)
--          → ⊢ Γ / (⊢ₗ• l lε n Bfalse nε)
--          → ⊢ Γ / lε
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
--    Emptyⱼ : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Empty
--    Unitⱼ  : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Unit
    Πⱼ_▹_  : ∀ {l : LCon} {lε : ⊢ₗ l}
           → Γ / lε     ⊢ F
           → Γ ∙ F / lε ⊢ G
           → Γ / lε     ⊢ Π F ▹ G
    Σⱼ_▹_  : ∀ {l : LCon} {lε : ⊢ₗ l} → Γ / lε     ⊢ F
           → Γ ∙ F / lε ⊢ G
           → Γ / lε     ⊢ Σ F ▹ G
    univ   : ∀ {l : LCon} {lε : ⊢ₗ l}
           → Γ / lε                        ⊢ A ∷ U
           → Γ / lε                        ⊢ A
    ϝⱼ      : ∀  {l lε F n nε}
           → (⊢Γ : ⊢ Γ / lε)
           → αNeutral {l = l} n F
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
--    Emptyⱼ    : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Empty ∷ U
--    Unitⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ Unit ∷ U

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
--    Emptyrecⱼ : ∀ {l : LCon} {lε : ⊢ₗ l} {A e}
--              → Γ / lε ⊢ A → Γ / lε ⊢ e ∷ Empty → Γ / lε ⊢ Emptyrec A e ∷ A

--    starⱼ     : ∀ {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ star ∷ Unit

    conv      : ∀ {l : LCon} {lε : ⊢ₗ l} {t A B}
              → Γ / lε ⊢ t ∷ A
              → Γ / lε ⊢ A ≡ B
              → Γ / lε ⊢ t ∷ B
    αⱼ : ∀ {l : LCon} {lε : ⊢ₗ l} {n}
              → Γ / lε ⊢ n ∷ ℕ
              → Γ / lε ⊢ α n ∷ 𝔹
    ϝⱼ-A : ∀ {l : LCon} {lε : ⊢ₗ l} {t A n nε}
              → (⊢Γ : ⊢ Γ / lε)
              → αNeutral {l = l} n A 
              → Γ / (⊢ₗ• l lε n Btrue nε)   ⊢ t ∷ A
              → Γ / (⊢ₗ• l lε n Bfalse nε)  ⊢ t ∷ A
              → Γ / lε                 ⊢ t ∷ A
    ϝⱼ-t : ∀ {l : LCon} {lε : ⊢ₗ l} {t A n nε}
              → (⊢Γ : ⊢ Γ / lε)
              → αNeutral {l = l} n t 
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
--    ϝ-cong : ∀  {l : LCon} {lε : ⊢ₗ l} {F G n nε}
--           → Γ / (⊢ₗ• l lε n Btrue nε)   ⊢ F ≡ G
--           → Γ / (⊢ₗ• l lε n Bfalse nε)  ⊢ F ≡ G
--           → Γ / lε                 ⊢ F ≡ G
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
--    Emptyrec-cong : ∀ {l : LCon} {lε : ⊢ₗ l} {A A' e e'}
--                  → Γ / lε ⊢ A ≡ A'
--                  → Γ / lε ⊢ e ≡ e' ∷ Empty
--                  → Γ / lε ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A
--    η-unit        : ∀ {l : LCon} {lε : ⊢ₗ l} {e e'}
--                  → Γ / lε ⊢ e ∷ Unit
--                  → Γ / lε ⊢ e' ∷ Unit
--                  → Γ / lε ⊢ e ≡ e' ∷ Unit
    α-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {m n}
                  → Γ / lε ⊢ m ≡ n ∷ ℕ
                  → Γ / lε ⊢ α m ≡ α n ∷ 𝔹
    ϝ-cong      : ∀ {l : LCon} {lε : ⊢ₗ l} {t u n nε}
                  → (⊢Γ : ⊢ Γ / lε)
                  → αNeutral {l = l} n t
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




-- mutual
--   ConBack : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
--            → ⊢ Γ / lε'
--            → ⊢ Γ / lε
--   ConBack f<  ε = ε
--   ConBack f<  (⊢Γ ∙ ⊢A) = ConBack f< ⊢Γ ∙ TyBack f< ⊢A

--   TyBack : ∀ {l l' : LCon} {A} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
--            → Γ / lε' ⊢ A
--            → Γ / lε ⊢ A
--   TyBack f<  (Uⱼ ⊢Γ) = Uⱼ (ConBack f<  ⊢Γ) 
--   TyBack f<  (ℕⱼ ⊢Γ) = ℕⱼ (ConBack f<  ⊢Γ)
--   TyBack f<  (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (ConBack f<  ⊢Γ)
-- --  TyBack f<  (Emptyⱼ ⊢Γ) = Emptyⱼ (ConBack f<  ⊢Γ)
-- --  TyBack f<  (Unitⱼ ⊢Γ) = Unitⱼ (ConBack f<  ⊢Γ)
--   TyBack f<  (Πⱼ A ▹ B) = Πⱼ TyBack f<  A ▹ TyBack f<  B
--   TyBack f<  (Σⱼ A ▹ B) = Σⱼ TyBack f<  A ▹ TyBack f<  B
--   TyBack f<  (univ u) = {!!} -- univ (TermBack f< u)
  
--   TermBack : ∀ {l l' : LCon} {t A} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} (≤ε : l ≤ₗ l')
--            → Γ / lε' ⊢ t ∷ A
--            → (Γ / lε' ⊢ t ∷ A) TS.⊎ ((∃ λ m → αNeutral m t) TS.⊎ (∃ λ m → αNeutral m A))
--   TermBack f<  (ℕⱼ ⊢Γ) = {!!} --  ℕⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (𝔹ⱼ ⊢Γ) = {!!} --  𝔹ⱼ (ConBack f<  ⊢Γ)
-- --  TermBack f<  (Emptyⱼ ⊢Γ) = ? --  Emptyⱼ (ConBack f<  ⊢Γ)
-- --  TermBack f<  (Unitⱼ ⊢Γ) = ? --  Unitⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (Πⱼ A ▹ B) = {!!} --  Πⱼ TermBack f<  A ▹ TermBack f<  B
--   TermBack f<  (Σⱼ A ▹ B) = {!!} --  Σⱼ TermBack f<  A ▹ TermBack f<  B
--   TermBack f<  (var ⊢Γ x) = {!!} --  var (ConBack f<  ⊢Γ) x
--   TermBack f<  (lamⱼ ⊢F x) = {!!} --  lamⱼ (TyBack f<  ⊢F) (TermBack f<  x)
--   TermBack f<  (t ∘ⱼ u) = {!!} --  TermBack f<  t ∘ⱼ TermBack f<  u
--   TermBack f<  (prodⱼ x x₁ x₂ x₃) = {!!} --  prodⱼ (TyBack f<  x) (TyBack f<  x₁) (TermBack f<  x₂) (TermBack f<  x₃)
--   TermBack f<  (fstⱼ x x₁ x₂) = {!!} --  fstⱼ (TyBack f<  x) (TyBack f<  x₁) (TermBack f<  x₂)
--   TermBack f<  (sndⱼ x x₁ x₂) = {!!} --  sndⱼ (TyBack f<  x) (TyBack f<  x₁) (TermBack f<  x₂)
--   TermBack f<  (zeroⱼ ⊢Γ) = {!!} --  zeroⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (sucⱼ ⊢n) = {!!} --  sucⱼ (TermBack f<  ⊢n)
--   TermBack f<  (natrecⱼ x x₁ x₂ x₃) = {!!} --  natrecⱼ (TyBack f<  x) (TermBack f<  x₁) (TermBack f<  x₂) (TermBack f<  x₃)
--   TermBack f<  (trueⱼ ⊢Γ) = {!!} --  trueⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (falseⱼ ⊢Γ) = {!!} --  falseⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (boolrecⱼ x x₁ x₂ x₃) = {!!} --  boolrecⱼ (TyBack f<  x) (TermBack f<  x₁) (TermBack f<  x₂) (TermBack f<  x₃)
-- --  TermBack f<  (Emptyrecⱼ x x₁) = ? --  Emptyrecⱼ (TyBack f<  x) (TermBack f<  x₁)
-- --  TermBack f<  (starⱼ ⊢Γ) = ? --  starⱼ (ConBack f<  ⊢Γ)
--   TermBack f<  (conv x x₁) = {!!} --  let help = TermBack f< x in {!!}
--   TermBack f<  (αⱼ x) = {!!} --  αⱼ (TermBack f< x)


NatToℕ : ∀ m {l : LCon} {lε : ⊢ₗ l} → ⊢ Γ / lε → Γ / lε ⊢ (natToTerm _ m) ∷ ℕ
NatToℕ 0 ⊢Γ = zeroⱼ ⊢Γ
NatToℕ (1+ m) ⊢Γ = sucⱼ (NatToℕ m ⊢Γ)

mutual
  Con≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'}
             → l ≤ₗ l'
             → ⊢ Γ / lε
             → ⊢ Γ / lε'
  Con≤ f< ε = ε
  Con≤ f<  (⊢Γ ∙ ⊢A) = Con≤ f< ⊢Γ ∙ Ty≤ f< ⊢A
  -- Con≤ {l' = l'} f< (ϝ {n = n} {nε = nε} g d) with decidInLConNat l' n
  -- Con≤ {l' = l'} f< (ϝ {n = n} {nε = nε} g d) | TS.inj₁ (TS.inj₁ inl' ) = Con≤ (≤ₗ-add _ _ _ f< inl') g
  -- Con≤ {l' = l'} f< (ϝ {n = n} {nε = nε} g d) | TS.inj₁ (TS.inj₂ inl' ) = Con≤ (≤ₗ-add _ _ _ f< inl') d
  -- Con≤ {l' = l'} f< (ϝ {n = n} {nε = nε} g d) | TS.inj₂ k = ϝ {_} {_} {_} {_} {_} {k} (Con≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat l')) g)
  --                                                             (Con≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat l')) d)

  Ty≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A}
          → l ≤ₗ l'
          → Γ / lε ⊢ A
          → Γ / lε' ⊢ A
  Ty≤ f< (Uⱼ ⊢Γ) = Uⱼ (Con≤ f< ⊢Γ)
  Ty≤ f< (ℕⱼ ⊢Γ) = ℕⱼ (Con≤ f< ⊢Γ)
  Ty≤ f< (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (Con≤ f< ⊢Γ)
--  Ty≤ f< (Emptyⱼ ⊢Γ) = Emptyⱼ (Con≤ f< ⊢Γ)
--  Ty≤ f< (Unitⱼ ⊢Γ) = Unitⱼ (Con≤ f< ⊢Γ)
  Ty≤ f< (Πⱼ A ▹ B) = Πⱼ Ty≤ f< A ▹ Ty≤ f< B 
  Ty≤ f< (Σⱼ A ▹ B) = Σⱼ Ty≤ f< A ▹ Ty≤ f< B 
  Ty≤ f< (univ u) = univ (Term≤ f< u)
  Ty≤ {l' = l'} f< (ϝⱼ {n = n} {nε = nε} ⊢Γ αA g d) with decidInLConNat l' n 
  Ty≤ f< (ϝⱼ {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₁ (TS.inj₁ inl' ) = Ty≤ (≤ₗ-add _ _ _ f< inl') g
  Ty≤ f< (ϝⱼ {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₁ (TS.inj₂ inl' ) = Ty≤ (≤ₗ-add _ _ _ f< inl') d
  Ty≤ f< (ϝⱼ {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₂ k =
    ϝⱼ {nε = k} (Con≤ f< ⊢Γ) (αNeNotIn k αA)
      (Ty≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) g)
      (Ty≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) d) --ϝⱼ {_} {_} {_} {_} {_} {_} {k}
  --                                                    (Ty≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) g)
  --                                                    (Ty≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) d)
                                                                             
  Term≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t}
          → l ≤ₗ l'
          → Γ / lε ⊢ t ∷ A
          → Γ / lε' ⊢ t ∷ A
  Term≤ f< (ℕⱼ ⊢Γ) = ℕⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (𝔹ⱼ ⊢Γ) = 𝔹ⱼ (Con≤ f< ⊢Γ)
--  Term≤ f< (Emptyⱼ ⊢Γ) = Emptyⱼ (Con≤ f< ⊢Γ)
--  Term≤ f< (Unitⱼ ⊢Γ) = Unitⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (Πⱼ A ▹ B) = Πⱼ Term≤ f< A ▹ Term≤ f< B 
  Term≤ f< (Σⱼ A ▹ B) = Σⱼ Term≤ f< A ▹ Term≤ f< B 
  Term≤ f< (var ⊢Γ x) = var (Con≤ f< ⊢Γ) x
  Term≤ f< (lamⱼ ⊢F x) = lamⱼ (Ty≤ f< ⊢F) (Term≤ f< x)
  Term≤ f< (t ∘ⱼ u) = Term≤ f< t ∘ⱼ Term≤ f< u
  Term≤ f< (prodⱼ x x₁ x₂ x₃) = prodⱼ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
  Term≤ f< (fstⱼ x x₁ x₂) = fstⱼ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂)
  Term≤ f< (sndⱼ x x₁ x₂) = sndⱼ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂)
  Term≤ f< (zeroⱼ ⊢Γ) = zeroⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (sucⱼ ⊢n) = sucⱼ (Term≤ f< ⊢n)
  Term≤ f< (natrecⱼ x x₁ x₂ x₃) = natrecⱼ (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
  Term≤ f< (trueⱼ ⊢Γ) = trueⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (falseⱼ ⊢Γ) = falseⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (boolrecⱼ x x₁ x₂ x₃) = boolrecⱼ (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
--  Term≤ f< (Emptyrecⱼ x x₁) = Emptyrecⱼ (Ty≤ f< x) (Term≤ f< x₁)
--  Term≤ f< (starⱼ ⊢Γ) = starⱼ (Con≤ f< ⊢Γ)
  Term≤ f< (conv x x₁) = conv (Term≤ f< x) (ConvTy≤ f< x₁)
  Term≤ f< (αⱼ x) = αⱼ (Term≤ f< x)
  Term≤ {l' = l'} f< (ϝⱼ-A {n = n} {nε = nε} ⊢Γ αA g d) with decidInLConNat l' n
  Term≤ f< (ϝⱼ-A {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₁ (TS.inj₁ inl' ) = Term≤ (≤ₗ-add _ _ _ f< inl') g
  Term≤ f< (ϝⱼ-A {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₁ (TS.inj₂ inl' ) = Term≤ (≤ₗ-add _ _ _ f< inl') d
  Term≤ f< (ϝⱼ-A {n = n} {nε = nε} ⊢Γ αA g d) | TS.inj₂ k =
    ϝⱼ-A {nε = k} (Con≤ f< ⊢Γ) (αNeNotIn k αA)
      (Term≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) g)
      (Term≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) d)
  Term≤ {l' = l'} f< (ϝⱼ-t {n = n} {nε = nε} ⊢Γ αA g d) with decidInLConNat l' n
  Term≤ f< (ϝⱼ-t {n = n} {nε = nε} ⊢Γ αt g d) | TS.inj₁ (TS.inj₁ inl' ) = Term≤ (≤ₗ-add _ _ _ f< inl') g
  Term≤ f< (ϝⱼ-t {n = n} {nε = nε} ⊢Γ αt g d) | TS.inj₁ (TS.inj₂ inl' ) = Term≤ (≤ₗ-add _ _ _ f< inl') d
  Term≤ f< (ϝⱼ-t {n = n} {nε = nε} ⊢Γ αt g d) | TS.inj₂ k =
    ϝⱼ-t {nε = k} (Con≤ f< ⊢Γ) (αNeNotIn k αt)
      (Term≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) g)
      (Term≤ (≤ₗ-add _ _ _ (≤ₗ-add-r f<) (InHereNat _)) d)
  --                                                   (Term≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) g)
  --                                                   (Term≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) d)
                                                     
  ConvTy≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A B}
            → l ≤ₗ l'
            → Γ / lε ⊢ A ≡ B
            → Γ / lε' ⊢ A ≡ B
  ConvTy≤ f< (univ t≡u) = univ (ConvTerm≤ f< t≡u) -- univ (Con≤vTerm lε n b nbε t≡u)
  ConvTy≤ f< (refl A) = refl (Ty≤ f< A) -- refl (Ty≤ lε n b nbε A)
  ConvTy≤ f< (sym A) = sym (ConvTy≤ f< A) -- sym (ConvTy≤ lε n b nbε A)
  ConvTy≤ f< (trans t≡u u≡v) = trans (ConvTy≤ f< t≡u) (ConvTy≤ f< u≡v) -- trans (ConvTy≤ lε n b nbε t≡u) (ConvTy≤ lε n b nbε u≡v)
  ConvTy≤ f< (Π-cong x x₁ x₂) = Π-cong (Ty≤ f< x) (ConvTy≤ f< x₁) (ConvTy≤ f< x₂)
  ConvTy≤ f< (Σ-cong x x₁ x₂) = Σ-cong (Ty≤ f< x) (ConvTy≤ f< x₁) (ConvTy≤ f< x₂)
  --ConvTy≤ {l' = l'} f< (ϝ-cong {n = n} {nε = nε} g d) with decidInLConNat l' n 
  --ConvTy≤ f< (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ (TS.inj₁ inl' ) = ConvTy≤ (≤ₗ-add _ _ _ f< inl') g
  --ConvTy≤ f< (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₁ (TS.inj₂ inl' ) = ConvTy≤ (≤ₗ-add _ _ _ f< inl') d
  --ConvTy≤ f< (ϝ-cong {n = n} {nε = nε} g d) | TS.inj₂ k = ϝ-cong {_} {_} {_} {_} {_} {_} {_} {k}
  --                                                   (ConvTy≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) g)
  --                                                   (ConvTy≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) d)
                                                     
  ConvTerm≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A t u}
              → l ≤ₗ l'
              → Γ / lε ⊢ t ≡ u ∷ A
              → Γ / lε' ⊢ t ≡ u ∷ A
  ConvTerm≤ f< (refl t) = refl (Term≤ f< t) -- refl (Term≤ lε n b nbε t)
  ConvTerm≤ f< (sym x) = sym (ConvTerm≤ f< x) -- sym (ConvTerm≤ lε n b nbε x)
  ConvTerm≤ f< (trans x x₁) = trans (ConvTerm≤ f< x) (ConvTerm≤ f< x₁) -- trans (ConvTerm≤ f< x) (ConvTerm≤ f< x₁)
  ConvTerm≤ f< (conv x x₁) = conv (ConvTerm≤ f< x) (ConvTy≤ f< x₁) -- conv (ConvTerm≤ lε n b nbε x) (ConvTy≤ lε n b nbε x₁)
  ConvTerm≤ f< (Π-cong x x₁ x₂) = Π-cong (Ty≤ f< x) (ConvTerm≤ f< x₁) (ConvTerm≤ f< x₂)
  ConvTerm≤ f< (Σ-cong x x₁ x₂) = Σ-cong (Ty≤ f< x) (ConvTerm≤ f< x₁) (ConvTerm≤ f< x₂)
  ConvTerm≤ f< (app-cong x x₁) = app-cong (ConvTerm≤ f< x) (ConvTerm≤ f< x₁)
  ConvTerm≤ f< (β-red x x₁ x₂) = β-red (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
  ConvTerm≤ f< (η-eq x x₁ x₂ x₃) = η-eq (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂) (ConvTerm≤ f< x₃)
  ConvTerm≤ f< (fst-cong x x₁ x₂) = fst-cong (Ty≤ f< x) (Ty≤ f< x₁) (ConvTerm≤ f< x₂)
  ConvTerm≤ f< (snd-cong x x₁ x₂) = snd-cong (Ty≤ f< x) (Ty≤ f< x₁) (ConvTerm≤ f< x₂)
  ConvTerm≤ f< (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
  ConvTerm≤ f< (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃) 
  ConvTerm≤ f< (Σ-η x x₁ x₂ x₃ x₄ x₅) = Σ-η (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃) (ConvTerm≤ f< x₄) (ConvTerm≤ f< x₅)
  ConvTerm≤ f< (suc-cong x) = suc-cong (ConvTerm≤ f< x) -- suc-cong (ConvTerm≤ lε n b nbε x)
  ConvTerm≤ f< (natrec-cong x x₁ x₂ x₃) = natrec-cong (ConvTy≤ f< x) (ConvTerm≤ f< x₁) (ConvTerm≤ f< x₂) (ConvTerm≤ f< x₃)
  ConvTerm≤ f< (natrec-zero x x₁ x₂) = natrec-zero (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
  ConvTerm≤ f< (natrec-suc x x₁ x₂ x₃) = natrec-suc (Term≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
  ConvTerm≤ f< (boolrec-cong x x₁ x₂ x₃) = boolrec-cong (ConvTy≤ f< x) (ConvTerm≤ f< x₁) (ConvTerm≤ f< x₂) (ConvTerm≤ f< x₃)
  ConvTerm≤ f< (boolrec-true x x₁ x₂) = boolrec-true (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
  ConvTerm≤ f< (boolrec-false x x₁ x₂) = boolrec-false (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
--  ConvTerm≤ f< (Emptyrec-cong x x₁) = Emptyrec-cong (ConvTy≤ f< x) (ConvTerm≤ f< x₁)
--  ConvTerm≤ f< (η-unit x x₁) = η-unit (Term≤ f< x) (Term≤ f< x₁) -- η-unit (Term≤ lε n b nbε x) (Term≤ lε n b nbε x₁)
  ConvTerm≤ f< (α-cong x) = α-cong (ConvTerm≤ f< x) -- α-cong (ConvTerm≤ lε n b nbε x)
  ConvTerm≤ {l' = l'} f< (ϝ-cong {n = n} {nε = nε} ⊢Γ αt g d) with decidInLConNat l' n 
  ConvTerm≤ f< (ϝ-cong {n = n} {nε = nε} ⊢Γ αt g d) | TS.inj₁ (TS.inj₁ inl' ) = ConvTerm≤ (≤ₗ-add _ _ _ f< inl') g
  ConvTerm≤ f< (ϝ-cong {n = n} {nε = nε} ⊢Γ αt g d) | TS.inj₁ (TS.inj₂ inl' ) = ConvTerm≤ (≤ₗ-add _ _ _ f< inl') d
  ConvTerm≤ f< (ϝ-cong ⊢Γ αt g d) | TS.inj₂ k =
    ϝ-cong {nε = k} (Con≤ f< ⊢Γ) (αNeNotIn k αt)
           (ConvTerm≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) g)
           (ConvTerm≤ (≤ₗ-add _ _ _ (λ n b inl → InThere _ (f< _ _ inl) _ _) (InHereNat _)) d)
  ConvTerm≤ f< (α-conv x y) = α-conv (Term≤ f< x) (f< _ _ y)
  


τCon : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε
         → ⊢ Γ / lε
         → ⊢ Γ / (⊢ₗ• l lε n b nbε)
τCon lε n b nbε ⊢Γ = Con≤ (λ n b inl → InThere _ inl _ _) ⊢Γ


τTy : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε
        → Γ / lε ⊢ A
          → Γ / (⊢ₗ• l lε n b nbε) ⊢ A
τTy lε n b nbε ⊢A = Ty≤ (λ n b inl → InThere _ inl _ _) ⊢A

τTerm : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {t}
          → Γ / lε ⊢ t ∷ A
          → Γ / (⊢ₗ• l lε n b nbε) ⊢ t ∷ A
τTerm lε n b nbε ⊢t = Term≤ (λ n b inl → InThere _ inl _ _) ⊢t

τConvTy : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {A B}
            → Γ / lε ⊢ A ≡ B
            → Γ / (⊢ₗ• l lε n b nbε) ⊢ A ≡ B
τConvTy lε n b nbε t≡u = ConvTy≤ (λ n b inl → InThere _ inl _ _) t≡u

τConvTerm : ∀ {l : LCon} (lε : ⊢ₗ l) n b nbε {A t u}
              → Γ / lε ⊢ t ≡ u ∷ A
              → Γ / (⊢ₗ• l lε n b nbε) ⊢ t ≡ u ∷ A
τConvTerm lε n b nbε t≡u = ConvTerm≤ (λ n b inl → InThere _ inl _ _) t≡u


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
--  Emptyrec-subst : ∀ {l : LCon} {lε : ⊢ₗ l} {  n n′ A}
--                 → Γ / lε     ⊢ A
--                 → Γ / lε     ⊢ n ⇒ n′ ∷ Empty
--                 → Γ / lε     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A
  α-subst        : ∀ {l : LCon} {lε : ⊢ₗ l} {  n n'}
                 → Γ / lε     ⊢ n ⇒ n' ∷ ℕ
                 → Γ / lε     ⊢ α n ⇒ α n' ∷ 𝔹
  α-red          : ∀ {l : LCon} {lε : ⊢ₗ l} {n b}
                 → Γ / lε     ⊢ n ∷ ℕ
                 → InLCon n b l
                 → Γ / lε     ⊢ α n ⇒ b ∷ 𝔹
                 


RedTerm≤ : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t u A}
             → l ≤ₗ l'
             → Γ / lε ⊢ t ⇒ u ∷ A
             → Γ / lε' ⊢ t ⇒ u ∷ A
RedTerm≤ f< (conv x x₁) = conv (RedTerm≤ f< x) (ConvTy≤ f< x₁)
RedTerm≤ f< (app-subst x x₁) = app-subst (RedTerm≤ f< x) (Term≤ f< x₁)
RedTerm≤ f< (β-red x x₁ x₂) = β-red (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
RedTerm≤ f< (fst-subst x x₁ x₂) = fst-subst (Ty≤ f< x) (Ty≤ f< x₁) (RedTerm≤ f< x₂)
RedTerm≤ f< (snd-subst x x₁ x₂) = snd-subst (Ty≤ f< x) (Ty≤ f< x₁) (RedTerm≤ f< x₂)
RedTerm≤ f< (Σ-β₁ x x₁ x₂ x₃) = Σ-β₁ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
RedTerm≤ f< (Σ-β₂ x x₁ x₂ x₃) = Σ-β₂ (Ty≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
RedTerm≤ f< (natrec-subst x x₁ x₂ x₃) = natrec-subst (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂) (RedTerm≤ f< x₃)
RedTerm≤ f< (natrec-zero x x₁ x₂) = natrec-zero (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
RedTerm≤ f< (natrec-suc x x₁ x₂ x₃) = natrec-suc (Term≤ f< x) (Ty≤ f< x₁) (Term≤ f< x₂) (Term≤ f< x₃)
RedTerm≤ f< (boolrec-subst x x₁ x₂ x₃) = boolrec-subst (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂) (RedTerm≤ f< x₃)
RedTerm≤ f< (boolrec-true x x₁ x₂) = boolrec-true (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
RedTerm≤ f< (boolrec-false x x₁ x₂) = boolrec-false (Ty≤ f< x) (Term≤ f< x₁) (Term≤ f< x₂)
-- RedTerm≤ f< (Emptyrec-subst x x₁) = Emptyrec-subst (Ty≤ f< x) (RedTerm≤ f< x₁)
RedTerm≤ f< (α-subst x₁) = α-subst (RedTerm≤ f< x₁)
RedTerm≤ f< (α-red ⊢n inl) = α-red (Term≤ f< ⊢n) (f< _ _ inl)

τRedTerm : ∀ {l : LCon} {lε : ⊢ₗ l} {t u A n b nε}
             → Γ / lε ⊢ t ⇒ u ∷ A
             → Γ / (⊢ₗ• l lε n b nε) ⊢ t ⇒ u ∷ A
τRedTerm d = RedTerm≤ (λ n b inl → InThere _ inl _ _) d          



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

⇒*-comp : ∀ {l : LCon} {lε : ⊢ₗ l} {A B C}
            → Γ / lε ⊢ A ⇒* B
            → Γ / lε ⊢ B ⇒* C
            → Γ / lε ⊢ A ⇒* C
⇒*-comp (id x) d' = d'
⇒*-comp (x ⇨ d) d' = x ⇨ ⇒*-comp d d'

Red≤* : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A B}
             → l ≤ₗ l'
             → Γ / lε ⊢ A ⇒* B
             → Γ / lε' ⊢ A ⇒* B
Red≤* f< (id d) = id (Ty≤ f< d)
Red≤* f< ((univ d) ⇨ d') = univ (RedTerm≤ f< d) ⇨ Red≤* f< d'

RedTerm≤* : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {t u A}
             → l ≤ₗ l'
             → Γ / lε ⊢ t ⇒* u ∷ A
             → Γ / lε' ⊢ t ⇒* u ∷ A
RedTerm≤* f< (id d) = id (Term≤ f< d)
RedTerm≤* f< (d ⇨ d') = (RedTerm≤ f< d) ⇨ RedTerm≤* f< d'                                 
             


τRed* : ∀ {l : LCon} {lε : ⊢ₗ l} {A B n b nε}
             → Γ / lε ⊢ A ⇒* B
             → Γ / (⊢ₗ• l lε n b nε) ⊢ A ⇒* B
τRed* (id d) = id (τTy _ _ _ _ d)
τRed* ((univ d) ⇨ d') = univ (τRedTerm d) ⇨ τRed* d'

τRed*Term : ∀ {l : LCon} {lε : ⊢ₗ l} {t u A n b nε}
             → Γ / lε ⊢ t ⇒* u ∷ A
             → Γ / (⊢ₗ• l lε n b nε) ⊢ t ⇒* u ∷ A
τRed*Term (id d) = id (τTerm _ _ _ _ d)
τRed*Term (d ⇨ d') = τRedTerm d ⇨ τRed*Term d'

-- Type reduction to whnf
_/_⊢_↘_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Set
_/_⊢_↘_ Γ {l = l} lε A B = Γ / lε ⊢ A ⇒* B × Whnf {l} B

-- Term reduction to whnf
_/_⊢_↘_∷_ : (Γ : Con Term n) → {l : LCon} → (lε : ⊢ₗ l) → Term n → Term n → Term n → Set
_/_⊢_↘_∷_ Γ {l = l} lε t u A = Γ / lε ⊢ t ⇒* u ∷ A × Whnf {l} u




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

wfRed≤* : ∀ {l l' : LCon} {lε : ⊢ₗ l} {lε' : ⊢ₗ l'} {A B}
             → l ≤ₗ l'
             → Γ / lε ⊢ A :⇒*: B
             → Γ / lε' ⊢ A :⇒*: B
wfRed≤* f< [ ⊢A , ⊢B , A⇨B ] = [ Ty≤ f< ⊢A , Ty≤ f< ⊢B , Red≤* f< A⇨B ]

τwfRed* : ∀ {l : LCon} {lε : ⊢ₗ l} {A B n b nε}
             → Γ / lε ⊢ A :⇒*: B
             → Γ / (⊢ₗ• l lε n b nε) ⊢ A :⇒*: B
τwfRed* [ ⊢A , ⊢B , A⇨B ] = [ τTy _ _ _ _ ⊢A , τTy _ _ _ _ ⊢B , τRed* A⇨B ]

          

open _/_⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

:⇒:*-comp : ∀ {l : LCon} {lε : ⊢ₗ l} {A B C}
             → Γ / lε ⊢ A :⇒*: B
             → Γ / lε ⊢ B :⇒*: C
             → Γ / lε ⊢ A :⇒*: C
:⇒:*-comp A⇒B B⇒C = [ ⊢A-red A⇒B , ⊢B-red B⇒C , ⇒*-comp (red A⇒B) (red B⇒C) ]

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
