{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Tools.Nat

private
  variable
    n : Nat
    l : LCon
    lε : ⊢ₗ l
    Γ : Con Term n
    A A′ B B′ : Term n
    a a′ b b′ : Term n

-- Weak head expansion of type equality
reduction : Γ / lε ⊢ A ⇒* A′
          → Γ / lε ⊢ B ⇒* B′
          → Whnf {l} {lε} A′
          → Whnf {l} {lε} B′
          → Γ / lε ⊢ A′ ≡ B′
          → Γ / lε ⊢ A ≡ B
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : Γ / lε ⊢ A ⇒* A′
           → Γ / lε ⊢ B ⇒* B′
           → Whnf {l} {lε} A′
           → Whnf {l} {lε} B′
           → Γ / lε ⊢ A ≡ B
           → Γ / lε ⊢ A′ ≡ B′
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : Γ / lε ⊢ A ⇒* B
           → Γ / lε ⊢ a ⇒* a′ ∷ B
           → Γ / lε ⊢ b ⇒* b′ ∷ B
           → Whnf {l} {lε} B
           → Whnf {l} {lε} a′
           → Whnf {l} {lε} b′
           → Γ / lε ⊢ a′ ≡ b′ ∷ B
           → Γ / lε ⊢ a ≡ b ∷ A
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : Γ / lε ⊢ A ⇒* B
            → Γ / lε ⊢ a ⇒* a′ ∷ B
            → Γ / lε ⊢ b ⇒* b′ ∷ B
            → Whnf {l} {lε} B
            → Whnf {l} {lε} a′
            → Whnf {l} {lε} b′
            → Γ / lε ⊢ a ≡ b ∷ A
            → Γ / lε ⊢ a′ ≡ b′ ∷ B
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
