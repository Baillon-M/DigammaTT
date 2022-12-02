-- Algorithmic equality.

{-# OPTIONS --without-K --safe #-}

module Definition.Conversion where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


infix 10 _/_⊢_~_↑_
infix 10 _/_⊢_~_↓_
infix 10 _/_⊢_[conv↑]_
infix 10 _/_⊢_[conv↓]_
infix 10 _/_⊢_[conv↑]_∷_
infix 10 _/_⊢_[conv↓]_∷_

private
  variable
    l : LCon
    n : Nat
    Γ : Con Term n

mutual
  -- Neutral equality.
  data _/_⊢_~_↑_ (Γ : Con Term n) (l : LCon) : (k j A : Term n) → Set where
    var-refl      : ∀ {x y A}
                  → Γ / l ⊢ var x ∷ A
                  → x PE.≡ y
                  → Γ / l ⊢ var x ~ var y ↑ A
    app-cong      : ∀ {k j t v F G}
                  → Γ / l ⊢ k ~ j ↓ Π F ▹ G
                  → Γ / l ⊢ t [conv↑] v ∷ F
                  → Γ / l ⊢ k ∘ t ~ j ∘ v ↑ G [ t ]
    fst-cong      : ∀ {p r F G}
                  → Γ / l ⊢ p ~ r ↓ Σ F ▹ G
                  → Γ / l ⊢ fst p ~ fst r ↑ F
    snd-cong      : ∀ {p r F G}
                  → Γ / l ⊢ p ~ r ↓ Σ F ▹ G
                  → Γ / l ⊢ snd p ~ snd r ↑ G [ fst p ]
    natrec-cong   : ∀ {k j h g a₀ b₀ F G}
                  → Γ ∙ ℕ / l ⊢ F [conv↑] G
                  → Γ / l ⊢ a₀ [conv↑] b₀ ∷ F [ zero ]
                  → Γ / l ⊢ h [conv↑] g ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ / l ⊢ k ~ j ↓ ℕ
                  → Γ / l ⊢ natrec F a₀ h k ~ natrec G b₀ g j ↑ F [ k ]
    Emptyrec-cong : ∀ {k j F G}
                  → Γ / l ⊢ F [conv↑] G
                  → Γ / l ⊢ k ~ j ↓ Empty
                  → Γ / l ⊢ Emptyrec F k ~ Emptyrec G j ↑ F
    α-cong        : ∀ {t u A}
                      {t′ u′ : Term n}
                      {D       : Γ / l ⊢ A ⇒* ℕ}
                      {d       : Γ / l ⊢ t ⇒* t′ ∷ ℕ}
                      {d′      : Γ / l ⊢ u ⇒* u′ ∷ ℕ}
                      {whnft′  : Whnf {l} t′}
                      {whnfu′  : Whnf {l} u′}
                    → (t<>u    : Γ / l ⊢ t′ [conv↓] u′ ∷ ℕ)
                    → ContainsNeutral t
                    → Γ / l ⊢ α t ~ α u ↑ 𝔹

  -- Neutral equality with types in WHNF.
  record _/_⊢_~_↓_ (Γ : Con Term n) (l : LCon) (k j B : Term n) : Set where
    inductive
    constructor [~]
    field
      A     : Term n
      D     : Γ / l ⊢ A ⇒* B
      whnfB : Whnf {l} B
      k~j   : Γ / l ⊢ k ~ j ↑ A

  -- Type equality.
  record _/_⊢_[conv↑]_ (Γ : Con Term n) (l : LCon) (A B : Term n) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term n
      D      : Γ / l ⊢ A ⇒* A′
      D′     : Γ / l ⊢ B ⇒* B′
      whnfA′ : Whnf {l} A′
      whnfB′ : Whnf {l} B′
      A′<>B′ : Γ / l ⊢ A′ [conv↓] B′

  -- Type equality with types in WHNF.
  data _/_⊢_[conv↓]_ (Γ : Con Term n) : (l : LCon) → (A B : Term n) → Set where
    U-refl     : ⊢ Γ / l → Γ / l ⊢ U [conv↓] U
    ℕ-refl     : ⊢ Γ / l → Γ / l ⊢ ℕ [conv↓] ℕ
    𝔹-refl     : ⊢ Γ / l → Γ / l ⊢ ℕ [conv↓] 𝔹
    Empty-refl : ⊢ Γ / l → Γ / l ⊢ Empty [conv↓] Empty
    Unit-refl  : ⊢ Γ / l → Γ / l ⊢ Unit [conv↓] Unit
    ne         : ∀ {K L}
               → Γ / l ⊢ K ~ L ↓ U
               → Γ / l ⊢ K [conv↓] L
    Π-cong     : ∀ {F G H E}
               → Γ / l ⊢ F
               → Γ / l ⊢ F [conv↑] H
               → Γ ∙ F / l ⊢ G [conv↑] E
               → Γ / l ⊢ Π F ▹ G [conv↓] Π H ▹ E
    Σ-cong     : ∀ {F G H E}
               → Γ / l ⊢ F
               → Γ / l ⊢ F [conv↑] H
               → Γ ∙ F / l ⊢ G [conv↑] E
               → Γ / l ⊢ Σ F ▹ G [conv↓] Σ H ▹ E

  -- Term equality.
  record _/_⊢_[conv↑]_∷_ (Γ : Con Term n) (l : LCon) (t u A : Term n) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term n
      D       : Γ / l ⊢ A ⇒* B
      d       : Γ / l ⊢ t ⇒* t′ ∷ B
      d′      : Γ / l ⊢ u ⇒* u′ ∷ B
      whnfB   : Whnf {l} B
      whnft′  : Whnf {l} t′
      whnfu′  : Whnf {l} u′
      t<>u    : Γ / l ⊢ t′ [conv↓] u′ ∷ B

  -- Term equality with types and terms in WHNF.
  data _/_⊢_[conv↓]_∷_ (Γ : Con Term n) : (l : LCon) → (t u A : Term n) → Set where
    ℕ-ins     : ∀ {k j}
              → Γ / l ⊢ k ~ j ↓ ℕ
              → Γ / l ⊢ k [conv↓] j ∷ ℕ
    Empty-ins : ∀ {k j}
              → Γ / l ⊢ k ~ j ↓ Empty
              → Γ / l ⊢ k [conv↓] j ∷ Empty
    Unit-ins  : ∀ {k j}
              → Γ / l ⊢ k ~ j ↓ Unit
              → Γ / l ⊢ k [conv↓] j ∷ Unit
    ne-ins    : ∀ {k j M N}
              → Γ / l ⊢ k ∷ N
              → Γ / l ⊢ j ∷ N
              → Neutral N
              → Γ / l ⊢ k ~ j ↓ M
              → Γ / l ⊢ k [conv↓] j ∷ N
    univ      : ∀ {A B}
              → Γ / l ⊢ A ∷ U
              → Γ / l ⊢ B ∷ U
              → Γ / l ⊢ A [conv↓] B
              → Γ / l ⊢ A [conv↓] B ∷ U
    zero-refl : ⊢ Γ / l → Γ / l ⊢ zero [conv↓] zero ∷ ℕ
    suc-cong  : ∀ {m n}
              → Γ / l ⊢ m [conv↑] n ∷ ℕ
              → Γ / l ⊢ suc m [conv↓] suc n ∷ ℕ
    true-refl : ⊢ Γ / l → Γ / l ⊢ true [conv↓] true ∷ 𝔹
    false-refl : ⊢ Γ / l → Γ / l ⊢ false [conv↓] false ∷ 𝔹
    η-eq      : ∀ {f g F G}
              → Γ / l ⊢ f ∷ Π F ▹ G
              → Γ / l ⊢ g ∷ Π F ▹ G
              → Function f
              → Function g
              → Γ ∙ F / l ⊢ wk1 f ∘ var x0 [conv↑] wk1 g ∘ var x0 ∷ G
              → Γ / l ⊢ f [conv↓] g ∷ Π F ▹ G
    Σ-η       : ∀ {p r F G}
              → Γ / l ⊢ p ∷ Σ F ▹ G
              → Γ / l ⊢ r ∷ Σ F ▹ G
              → Product p
              → Product r
              → Γ / l ⊢ fst p [conv↑] fst r ∷ F
              → Γ / l ⊢ snd p [conv↑] snd r ∷ G [ fst p ]
              → Γ / l ⊢ p [conv↓] r ∷ Σ F ▹ G
    η-unit    : ∀ {k j}
              → Γ / l ⊢ k ∷ Unit
              → Γ / l ⊢ j ∷ Unit
              → Whnf {l} k
              → Whnf {l} j
              → Γ / l ⊢ k [conv↓] j ∷ Unit
    α-NotInL  : ∀ {k j}
              → Γ / l ⊢ k [conv↓] j ∷ ℕ
              → NotInLCon k l
              → Γ / l ⊢ α k [conv↓] α j ∷ 𝔹
    α-InL     : ∀ {k b}
              → ⊢ Γ / l
              → InLCon k b l
              → Γ / l ⊢ α k [conv↓] b ∷ 𝔹
star-refl : ⊢ Γ / l → Γ / l ⊢ star [conv↓] star ∷ Unit
star-refl ⊢Γ = η-unit (starⱼ ⊢Γ) (starⱼ ⊢Γ) starₙ starₙ
