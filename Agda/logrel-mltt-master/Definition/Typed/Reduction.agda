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
    Γ : Con Term n
    A A′ B B′ : Term n
    a a′ b b′ : Term n

-- Weak head expansion of type equality
reduction : Γ / l ⊢ A ⇒* A′
          → Γ / l ⊢ B ⇒* B′
          → Whnf {l} A′
          → Whnf {l} B′
          → Γ / l ⊢ A′ ≡ B′
          → Γ / l ⊢ A ≡ B
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : Γ / l ⊢ A ⇒* A′
           → Γ / l ⊢ B ⇒* B′
           → Whnf {l} A′
           → Whnf {l} B′
           → Γ / l ⊢ A ≡ B
           → Γ / l ⊢ A′ ≡ B′
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : Γ / l ⊢ A ⇒* B
           → Γ / l ⊢ a ⇒* a′ ∷ B
           → Γ / l ⊢ b ⇒* b′ ∷ B
           → Whnf {l} B
           → Whnf {l} a′
           → Whnf {l} b′
           → Γ / l ⊢ a′ ≡ b′ ∷ B
           → Γ / l ⊢ a ≡ b ∷ A
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : Γ / l ⊢ A ⇒* B
            → Γ / l ⊢ a ⇒* a′ ∷ B
            → Γ / l ⊢ b ⇒* b′ ∷ B
            → Whnf {l} B
            → Whnf {l} a′
            → Whnf {l} b′
            → Γ / l ⊢ a ≡ b ∷ A
            → Γ / l ⊢ a′ ≡ b′ ∷ B
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
