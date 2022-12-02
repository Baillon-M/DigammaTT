{-# OPTIONS --without-K --safe #-}

module Definition.Typed.RedSteps where

open import Definition.Untyped
open import Definition.Typed
open import Tools.Nat

private
  variable
    n : Nat
    l : LCon
    lε : ⊢ₗ l
    Γ : Con Term n
    A B C : Term n
    a t t′ u r : Term n

-- Concatenation of type reduction closures
_⇨*_ : Γ / lε ⊢ A ⇒* B → Γ / lε ⊢ B ⇒* C → Γ / lε ⊢ A ⇒* C
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : Γ / lε ⊢ t ⇒* u ∷ A → Γ / lε ⊢ u ⇒* r ∷ A → Γ / lε ⊢ t ⇒* r ∷ A
id ⊢u ⇨∷* u⇒r = u⇒r
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒r = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒r)

-- Conversion of reduction closures
conv* : Γ / lε ⊢ t ⇒* u ∷ A → Γ / lε ⊢ A ≡ B → Γ / lε ⊢ t ⇒* u ∷ B
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

-- Universe of reduction closures
univ* : Γ / lε ⊢ A ⇒* B ∷ U → Γ / lε ⊢ A ⇒* B
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

-- Application substitution of reduction closures
app-subst* : Γ / lε ⊢ t ⇒* t′ ∷ Π A ▹ B → Γ / lε ⊢ a ∷ A
           → Γ / lε ⊢ t ∘ a ⇒* t′ ∘ a ∷ B [ a ]
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁
