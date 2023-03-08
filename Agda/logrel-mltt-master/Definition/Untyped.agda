-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --safe #-}

module Definition.Untyped where

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.List
open import Tools.Sum renaming (id to toto)
import Tools.PropositionalEquality as PE


infixl 30 _∙_
infix 30 Π_▹_
infixr 22 _▹▹_
infix 30 Σ_▹_
infixr 22 _××_
infix 30 ⟦_⟧_▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑


-- Typing contexts (length indexed snoc-lists, isomorphic to lists).
-- Terms added to the context are well scoped in the sense that it cannot
-- contain more unbound variables than can be looked up in the context.

data Con (A : Nat → Set) : Nat → Set where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

private
  variable
    n m ℓ : Nat

-- Representation of sub terms using a list of binding levels

data GenTs (A : Nat → Set) : Nat → List Nat → Set where
  []  : {n : Nat} → GenTs A n []
  _∷_ : {n b : Nat} {bs : List Nat} (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

-- Kinds are indexed on the number of expected sub terms
-- and the number of new variables bound by each sub term

data Kind : (ns : List Nat) → Set where
  Ukind : Kind []

  Pikind  : Kind (0 ∷ 1 ∷ [])
  Lamkind : Kind (1 ∷ [])
  Appkind : Kind (0 ∷ 0 ∷ [])

  Sigmakind : Kind (0 ∷ 1 ∷ [])
  Prodkind  : Kind (0 ∷ 0 ∷ [])
  Fstkind   : Kind (0 ∷ [])
  Sndkind   : Kind (0 ∷ [])

  Natkind    : Kind []
  Zerokind   : Kind []
  Suckind    : Kind (0 ∷ [])
  Natreckind : Kind (1 ∷ 0 ∷ 0 ∷ 0 ∷ [])

  Boolkind    : Kind []
  Truekind    : Kind []
  Falsekind   : Kind []
  αkind       : Kind (0 ∷ [])
  Boolreckind : Kind (1 ∷ 0 ∷ 0 ∷ 0 ∷ [])

--  Unitkind : Kind []
--  Starkind : Kind []

--  Emptykind    : Kind []
--  Emptyreckind : Kind (0 ∷ 0 ∷ [])

-- Terms are indexed by its number of unbound variables and are either:
-- de Bruijn style variables or
-- generic terms, formed by their kind and sub terms

data Term (n : Nat) : Set where
  var : (x : Fin n) → Term n
  gen : {bs : List Nat} (k : Kind bs) (c : GenTs Term n bs) → Term n

private
  variable
    A F H t b u v : Term n
    B E G       : Term (1+ n)

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U      : Term n                      -- Universe.
U = gen Ukind []

Π_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent function type (B is a binder).
Π A ▹ B = gen Pikind (A ∷ B ∷ [])

Σ_▹_ : (A : Term n) (B : Term (1+ n)) → Term n  -- Dependent sum type (B is a binder).
Σ A ▹ B = gen Sigmakind (A ∷ B ∷ [])

ℕ      : Term n                      -- Type of natural numbers.
ℕ = gen Natkind []

𝔹      : Term n                      -- Type of Booleans.
𝔹 = gen Boolkind []

-- Empty : Term n                       -- Empty type
-- Empty = gen Emptykind []

-- Unit  : Term n                       -- Unit type
-- Unit = gen Unitkind []

lam    : (t : Term (1+ n)) → Term n  -- Function abstraction (binder).
lam t = gen Lamkind (t ∷ [])

_∘_    : (t u : Term n) → Term n     -- Application.
t ∘ u = gen Appkind (t ∷ u ∷ [])


prod : (t u : Term n) → Term n       -- Dependent products
prod t u = gen Prodkind (t ∷ u ∷ [])

fst : (t : Term n) → Term n          -- First projection
fst t = gen Fstkind (t ∷ [])

snd : (t : Term n) → Term n          -- Second projection
snd t = gen Sndkind (t ∷ [])

-- Introduction and elimination of natural numbers.
zero   : Term n                      -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term n)       → Term n -- Successor.
suc t = gen Suckind (t ∷ [])

natrec : (A : Term (1+ n)) (t u v : Term n) → Term n  -- Natural number recursor (A is a binder).
natrec A t u v = gen Natreckind (A ∷ t ∷ u ∷ v ∷ [])

-- Introduction and elimination of booleans.
true   : Term n                      -- Boolean true.
true = gen Truekind []

false  : Term n                      -- Boolean false.
false = gen Falsekind []

α    : (t : Term n)       → Term n -- Successor.
α t = gen αkind (t ∷ [])

boolrec : (A : Term (1+ n)) (t u v : Term n) → Term n  -- Boolean recursor (A is a binder).
boolrec A t u v = gen Boolreckind (A ∷ t ∷ u ∷ v ∷ [])

-- star : Term n                        -- Unit element
-- star = gen Starkind []

-- Emptyrec : (A e : Term n) → Term n   -- Empty type recursor
-- Emptyrec A e = gen Emptyreckind (A ∷ e ∷ [])

-- Binding types

data BindingType : Set where
  BΠ : BindingType
  BΣ : BindingType

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BΠ ⟧ F ▹ G = Π F ▹ G
⟦ BΣ ⟧ F ▹ G = Σ F ▹ G

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  W F G = W H E  then  F = H  and  G = E.

B-PE-injectivity : ∀ W → ⟦ W ⟧ F ▹ G PE.≡ ⟦ W ⟧ H ▹ E → F PE.≡ H × G PE.≡ E
B-PE-injectivity BΠ PE.refl = PE.refl , PE.refl
B-PE-injectivity BΣ PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : suc t PE.≡ suc u → t PE.≡ u
suc-PE-injectivity PE.refl = PE.refl


-- If  α n = α m  then  n = m.

α-PE-injectivity : α t PE.≡ α u → t PE.≡ u
α-PE-injectivity PE.refl = PE.refl

data TrueNat {n : Nat} : Term n → Set where
  Truezero : TrueNat zero
  Truesuc : TrueNat t → TrueNat (suc t)


data Bbool : Set where
  Btrue : Bbool
  Bfalse : Bbool


data TrueBool {n : Nat} : Term n → Set where
  Truetrue : TrueBool true
  Truefalse : TrueBool false


data LCon : Set where
  εₗ   :                             LCon        -- Empty context.
  addₗ : Nat → Bbool → LCon → LCon   -- Context extension.


natToTerm : ∀ (n t : Nat) → Term n
natToTerm n Nat.zero = zero
natToTerm n (1+ t) = suc (natToTerm n t)

TrueNatToTerm : ∀ (n t : Nat) → TrueNat (natToTerm n t)
TrueNatToTerm n Nat.zero = Truezero
TrueNatToTerm n (1+ t) = Truesuc (TrueNatToTerm n t)

BboolToTerm : ∀ (n : Nat) (b : Bbool) → Term n
BboolToTerm n Btrue = true
BboolToTerm n Bfalse = false

TrueBboolToTerm : ∀ (n : Nat) (b : Bbool) → TrueBool (BboolToTerm n b)
TrueBboolToTerm n Btrue = Truetrue
TrueBboolToTerm n Bfalse = Truefalse


data InLCon {n : Nat} (t u : Term n) : LCon → Set
  where
    InHere :  ∀ (m : Nat) (b : Bbool) (t=m : t PE.≡ natToTerm n m) (u=b : u PE.≡ BboolToTerm n b) (γ : LCon) → InLCon t u (addₗ m b γ)
    InThere :  ∀ (γ : LCon) (γε : InLCon t u γ) (m : Nat) (b' : Bbool) → InLCon t u (addₗ m b' γ)

data InLConNat (t : Nat) (u : Bbool) : LCon → Set
  where
    InHereNat :  ∀ (γ : LCon) → InLConNat t u (addₗ t u γ)
    InThereNat :  ∀ (γ : LCon) (γε : InLConNat t u γ) (m : Nat) (b' : Bbool) → InLConNat t u (addₗ m b' γ)


data DifferentNat : ∀ (t u : Nat) → Set where
  Diff0r : ∀ t → DifferentNat (1+ t) 0
  Diff0l : ∀ t → DifferentNat 0 (1+ t)
  DiffSuc : ∀ (t u : Nat) → DifferentNat t u → DifferentNat (1+ t) (1+ u)
  

data DifferentTrueNat {n : Nat} : ∀ (t u : Term n) → Set where
  Diff0rTrueNat : ∀ (t : Term n) (tε : TrueNat t) → DifferentTrueNat (suc t) zero
  Diff0lTrueNat : ∀ (t : Term n) (tε : TrueNat t) → DifferentTrueNat zero (suc t)
  DiffSucTrueNat : ∀ (t u : Term n) → DifferentTrueNat t u → DifferentTrueNat (suc t) (suc u)
  
                
data NotInLCon {n : Nat} (t : Term n) : LCon → Set
  where
    NotInε : TrueNat t → NotInLCon t εₗ 
    NotInThere : ∀ (γ : LCon) (γε : NotInLCon t γ) (m : Nat) (b : Bbool) → DifferentTrueNat t (natToTerm n m) → NotInLCon t (addₗ m b γ)

data NotInLConNat (n : Nat) : LCon → Set
  where 
    NotInεNat : NotInLConNat n εₗ 
    NotInThereNat : ∀ (γ : LCon) (γε : NotInLConNat n γ) (m : Nat) (b : Bbool) → DifferentNat n m → NotInLConNat n (addₗ m b γ)

data ⊢ₗ_ : LCon → Set
  where
    ⊢ₗₑ : ⊢ₗ εₗ
    ⊢ₗ• : ∀ (γ : LCon) (γε : ⊢ₗ γ) (n : Nat) (b : Bbool) (nbε : NotInLConNat n γ) → ⊢ₗ (addₗ n b γ) 

permut : ∀ (n : Nat) (l : LCon) → LCon
permut n εₗ = εₗ
permut 0 (addₗ n2 b2 εₗ) = addₗ n2 b2 εₗ
permut 0 (addₗ n1 b1 (addₗ n2 b2 l)) = (addₗ n2 b2 (addₗ n1 b1 l))
permut (1+ n) (addₗ n1 b1 l) = addₗ n1 b1 (permut n l)

_≤ₗ_ : LCon → LCon → Set
_≤ₗ_ l l' = ∀ {n} (t u : Term n) → InLCon t u l → InLCon t u l'

suc-inj : ∀ {n} {t u : Term n} (e : suc t PE.≡ suc u) → t PE.≡ u
suc-inj PE.refl = PE.refl

EqNatToTermEqNat : ∀ {n} m k → natToTerm n m PE.≡ natToTerm n k → m PE.≡ k
EqNatToTermEqNat 0 0 PE.refl = PE.refl
EqNatToTermEqNat 0 (1+ k) ()
EqNatToTermEqNat (1+ n) 0 ()
EqNatToTermEqNat (1+ n) (1+ k) e = PE.cong 1+ (EqNatToTermEqNat n k (suc-inj e))

EqBboolToTermEqBbool : ∀ {n} m k → BboolToTerm n m PE.≡ BboolToTerm n k → m PE.≡ k
EqBboolToTermEqBbool Btrue Btrue PE.refl = PE.refl
EqBboolToTermEqBbool Btrue Bfalse ()
EqBboolToTermEqBbool Bfalse Btrue ()
EqBboolToTermEqBbool Bfalse Bfalse e = PE.refl


InLConNatInLCon : ∀ {n m b l} → InLConNat m b l → InLCon {n} (natToTerm _ m) (BboolToTerm _ b) l
InLConNatInLCon (InHereNat l) = InHere _ _ PE.refl PE.refl l
InLConNatInLCon (InThereNat l inl m b') = InThere l (InLConNatInLCon inl) m b'

InLConInLConNat : ∀ {n t u m b l} → t PE.≡ natToTerm _ m → u PE.≡ BboolToTerm _ b → InLCon {n} t u l → InLConNat m b l
InLConInLConNat PE.refl PE.refl (InHere m b t=m u=b l) rewrite EqNatToTermEqNat _ _ t=m rewrite EqBboolToTermEqBbool _ _ u=b  = InHereNat l
InLConInLConNat e1 e2 (InThere l inl m b') = InThereNat l (InLConInLConNat e1 e2 inl) m b'


-- data _≤ₗ_ : ∀ (l : LCon) → LCon → Set
--  where
--    ≤ₗ-refl : ∀ {l} → l ≤ₗ l
--    ≤ₗ-add : ∀ {l} n b l' → l ≤ₗ l' → l ≤ₗ (addₗ n b l')
--    ≤ₗ-perm : ∀ {l} n1 n2 b1 b2 l' → addₗ n1 b1 (addₗ n2 b2 l) ≤ₗ l' → (addₗ n2 b2 (addₗ n1 b1 l)) ≤ₗ l'

≤ₗ-id : ∀ l → l ≤ₗ l
≤ₗ-id l n b inl = inl

≤ₗ-• : ∀ {l l' l''} → l ≤ₗ l' → l' ≤ₗ l'' → l ≤ₗ l''
≤ₗ-• f< f<' n b inl = f<' n b (f< n b inl)

≤ₗ-add : ∀ {l} n b l' → l ≤ₗ l' → InLConNat n b l' → (addₗ n b l) ≤ₗ l'
≤ₗ-add n b l' f< inl' t u  (InHere n b t=n u=m l) rewrite u=m rewrite t=n = InLConNatInLCon inl'
≤ₗ-add n b l' f< inl' t u  (InThere l inl m b) = f< _ _ inl

≤ₗ-add-r : ∀ {l n b l'} → l ≤ₗ l' → l ≤ₗ (addₗ n b l')
≤ₗ-add-r f< n b inl = InThere _ (f< _ _ inl) _ _

≤ₗ-rev-l : ∀ {l l' m b} → (addₗ m b l) ≤ₗ l' → l ≤ₗ l'
≤ₗ-rev-l {l = l} {m = m} {b = b} f t u inl = f t u (InThere l inl m b)

Suc≠0 : ∀ n → (1+ n) PE.≡ 0 → PE.⊥
Suc≠0 n ()

Suc= : ∀ n m → (1+ n) PE.≡ (1+ m) → n PE.≡ m
Suc= n m PE.refl = PE.refl


DifferentNatDifferent : ∀ (t u : Nat) → DifferentNat t u → t PE.≡ u → PE.⊥
DifferentNatDifferent _ _ (Diff0l u) ()
DifferentNatDifferent _ _ (Diff0r t) ()
DifferentNatDifferent _ _ (DiffSuc t u tuε) PE.refl = DifferentNatDifferent t t tuε PE.refl

DifferentDifferentNat : ∀ (n m : Nat) → (n PE.≡ m → PE.⊥) → DifferentNat n m
DifferentDifferentNat 0 0 neq = PE.⊥-elim (neq PE.refl)
DifferentDifferentNat 0 (1+ m) neq = Diff0l m
DifferentDifferentNat (1+ n) 0 neq = Diff0r n
DifferentDifferentNat (1+ n) (1+ m) neq = DiffSuc n m (DifferentDifferentNat n m λ e → neq (PE.cong 1+ e))

DifferentNatSym : ∀ (n m : Nat) (n≠m : DifferentNat n m) → DifferentNat m n
DifferentNatSym _ _ (Diff0l u)  = Diff0r u
DifferentNatSym _ _ (Diff0r t) = Diff0l t
DifferentNatSym _ _ (DiffSuc t u tuε) = DiffSuc u t (DifferentNatSym t u tuε)

DifferentNatHProp :  ∀ (n m : Nat) (e e' : DifferentNat n m) → e PE.≡ e'
DifferentNatHProp _ _ (Diff0l u) (Diff0l u)  = PE.refl
DifferentNatHProp _ _ (Diff0r t) (Diff0r u) = PE.refl
DifferentNatHProp _ _ (DiffSuc t u tuε) (DiffSuc t u tuε') rewrite DifferentNatHProp t u tuε tuε' = PE.refl

NotInLConNatHProp : ∀ (n : Nat) (l : LCon) (nε nε' : NotInLConNat n l) → nε PE.≡ nε'
NotInLConNatHProp n εₗ NotInεNat NotInεNat = PE.refl
NotInLConNatHProp n (addₗ m b γ) (NotInThereNat _ nε .m .b e) (NotInThereNat .γ nε' .m .b e') rewrite (NotInLConNatHProp n γ nε nε') rewrite DifferentNatHProp _ _ e e' = PE.refl

⊢ₗ-HProp : ∀ l (lε lε' : ⊢ₗ l) → lε PE.≡ lε'
⊢ₗ-HProp εₗ  ⊢ₗₑ  ⊢ₗₑ = PE.refl
⊢ₗ-HProp (addₗ n b γ) (⊢ₗ• l lε n b nbε) (⊢ₗ• l lε' n b nbε') rewrite (NotInLConNatHProp n γ nbε nbε') rewrite ⊢ₗ-HProp l lε lε' = PE.refl

DifferentTrueNatDifferent : ∀ (t u : Term n) → DifferentTrueNat t u → t PE.≡ u → PE.⊥
DifferentTrueNatDifferent _ _ (Diff0lTrueNat u uε) ()
DifferentTrueNatDifferent _ _ (Diff0rTrueNat t tε) ()
DifferentTrueNatDifferent _ _ (DiffSucTrueNat t t tuε) PE.refl = DifferentTrueNatDifferent t t tuε PE.refl

DifferentDifferentTrueNat : ∀ {k m : Term n} → TrueNat k → TrueNat m → (k PE.≡ m → PE.⊥) → DifferentTrueNat k m
DifferentDifferentTrueNat Truezero Truezero neq = PE.⊥-elim (neq PE.refl)
DifferentDifferentTrueNat Truezero (Truesuc m) neq = Diff0lTrueNat _ m
DifferentDifferentTrueNat (Truesuc n) Truezero neq = Diff0rTrueNat _ n
DifferentDifferentTrueNat (Truesuc n) (Truesuc m) neq = DiffSucTrueNat _ _ (DifferentDifferentTrueNat n m λ e → neq (PE.cong suc e))

DifferentNatDifferentTrueNat : ∀ (k m : Nat) (t u : Term n) → DifferentNat k m → t PE.≡ natToTerm n k → u PE.≡ natToTerm n m → DifferentTrueNat t u
DifferentNatDifferentTrueNat _ _ _ _ (Diff0l u) e1 e2 rewrite e1 rewrite e2 = Diff0lTrueNat _ (TrueNatToTerm _ _)
DifferentNatDifferentTrueNat _ _ _ _ (Diff0r u) e1 e2 rewrite e1 rewrite e2 = Diff0rTrueNat _ (TrueNatToTerm _ _)
DifferentNatDifferentTrueNat _ _ _ _ (DiffSuc t u t≠u) e1 e2 rewrite e1 rewrite e2 = DiffSucTrueNat _ _ (DifferentNatDifferentTrueNat t u _ _ t≠u PE.refl PE.refl)

NotInLConNatNotInLCon : ∀ (t : Term n) m l → NotInLConNat m l → t PE.≡ natToTerm n m → NotInLCon t l
NotInLConNatNotInLCon t m εₗ NotInεNat e rewrite e = NotInε (TrueNatToTerm _ _)
NotInLConNatNotInLCon t m (addₗ n b l) (NotInThereNat l lε n b m≠n) e rewrite e = NotInThere l (NotInLConNatNotInLCon _ m l lε PE.refl) n b (DifferentNatDifferentTrueNat m n _ _ m≠n PE.refl PE.refl)

NotInLConNotInLCon : ∀ (t b : Term n) l → NotInLCon t l → InLCon t b l → PE.⊥
NotInLConNotInLCon t b εₗ _ ()
NotInLConNotInLCon t u (addₗ n b l) (NotInThere l lε n b notn) (InHere n b t=n u=m l) rewrite t=n = DifferentTrueNatDifferent _ _ notn PE.refl
NotInLConNotInLCon _ _ (addₗ n b l) (NotInThere l notlε n b notn) (InThere l lε n b) = NotInLConNotInLCon _ _ l notlε lε

NotInLCon≤ₗ : ∀ {l l'} {t : Term n} {m b} → ((addₗ m b l) ≤ₗ l') → NotInLCon t l' → t PE.≡ (natToTerm n m) → PE.⊥
NotInLCon≤ₗ f≤ notinl e = NotInLConNotInLCon _ _ _ notinl (f≤ _ _ (InHere _ _ e PE.refl _))

≤ₗ-rev-r : ∀ {l l' m b} → l ≤ₗ (addₗ m b l') → NotInLConNat m l → l ≤ₗ l'
≤ₗ-rev-r {m = m} {b = b} f< nε n b' inl with f< n b' inl
≤ₗ-rev-r {m = m} {b = b} f< nε n b' inl | InHere m b PE.refl PE.refl l' =
  PE.⊥-elim (NotInLConNotInLCon _ _ _ (NotInLConNatNotInLCon _ _ _ nε PE.refl) inl)
≤ₗ-rev-r {m = m} {b = b} f< nε n b' inl | InThere l' inl' _ _ = inl'

≤εEq : ∀ {l} (≤ε : l ≤ₗ εₗ) → l PE.≡ εₗ
≤εEq {l = εₗ} ≤ε = PE.refl
≤εEq {l = addₗ m b l} ≤ε with (≤ε {n = 0} _ _ (InHere m b PE.refl PE.refl l))
≤εEq {l = addₗ n b l} ≤ε | ()


decidEqNat : ∀ (n m : Nat) → (n PE.≡ m) ⊎ (n PE.≡ m → PE.⊥)
decidEqNat 0 0 = inj₁ PE.refl
decidEqNat (1+ n) 0 = inj₂ (Suc≠0 n)
decidEqNat 0 (1+ m) = inj₂ λ e → Suc≠0 m (PE.sym e)
decidEqNat (1+ n) (1+ m) with decidEqNat n m 
decidEqNat (1+ n) (1+ m) | inj₁ e rewrite e = inj₁ PE.refl
decidEqNat (1+ n) (1+ m) | inj₂ neq = inj₂ λ e → neq (Suc= n m e)



decidEqTrueNat :  ∀ (t u : Term n) (tε : TrueNat t) (uε : TrueNat u) → (t PE.≡ u) ⊎ (DifferentTrueNat t u)
decidEqTrueNat zero zero Truezero Truezero = inj₁ PE.refl
decidEqTrueNat .(suc _) .zero (Truesuc tε) Truezero = inj₂ (Diff0rTrueNat _ tε)
decidEqTrueNat zero .(suc _) Truezero (Truesuc uε) = inj₂ (Diff0lTrueNat _ uε)
decidEqTrueNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε)
  with decidEqTrueNat _ _ tε uε
decidEqTrueNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) | inj₁ k rewrite k = inj₁ PE.refl
decidEqTrueNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) | inj₂ k = inj₂ (DiffSucTrueNat _ _ k)

EqNatEqTrueNat : ∀ (t u : Term n) (tε : TrueNat t) (uε : TrueNat u) (e : t PE.≡ u) → (PE.subst TrueNat e tε PE.≡ uε)
EqNatEqTrueNat zero zero Truezero Truezero PE.refl = PE.refl
EqNatEqTrueNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) PE.refl = PE.cong Truesuc (EqNatEqTrueNat _ _ tε uε PE.refl)

decidInLCon : ∀ (γ : LCon) (t : Term n) (tε : TrueNat t) → ((InLCon t true γ) ⊎ (InLCon t false γ)) ⊎ (NotInLCon t γ)
decidInLCon εₗ t tε = inj₂ (NotInε tε)
decidInLCon (addₗ m b γ) t tε with decidEqTrueNat _ _ tε (TrueNatToTerm _ m)
decidInLCon (addₗ m Btrue γ) t tε | inj₁ k rewrite k rewrite (PE.sym (EqNatEqTrueNat _ _ (TrueNatToTerm _ m) tε PE.refl)) = inj₁ (inj₁ (InHere _ _ PE.refl PE.refl γ))
decidInLCon (addₗ m Bfalse γ) t tε | inj₁ k rewrite k rewrite (PE.sym (EqNatEqTrueNat _ _ (TrueNatToTerm _ m) tε PE.refl)) = inj₁ (inj₂ (InHere _ _ PE.refl PE.refl γ))
decidInLCon (addₗ m b γ) t tε | inj₂ k with decidInLCon γ t tε
decidInLCon (addₗ m b' γ) t tε | inj₂ k | inj₁ (inj₁ j) = inj₁ (inj₁ (InThere γ j m b'))
decidInLCon (addₗ m b' γ) t tε | inj₂ k | inj₁ (inj₂ j) = inj₁ (inj₂ (InThere γ j m b'))
decidInLCon (addₗ m b γ) t tε | inj₂ k | inj₂ j = inj₂ (NotInThere γ j m b k)

decidInLConNat : ∀ (γ : LCon) (t : Nat) → ((InLConNat t Btrue γ) ⊎ (InLConNat t Bfalse γ)) ⊎ (NotInLConNat t γ)
decidInLConNat εₗ t = inj₂ (NotInεNat)
decidInLConNat (addₗ m b γ) n with decidEqNat m n
decidInLConNat (addₗ m Btrue γ) t | inj₁ k rewrite k = inj₁ (inj₁ (InHereNat γ))
decidInLConNat (addₗ m Bfalse γ) t | inj₁ k rewrite k  = inj₁ (inj₂ (InHereNat γ))
decidInLConNat (addₗ m b γ) t | inj₂ k with decidInLConNat γ t
decidInLConNat (addₗ m b' γ) t | inj₂ k | inj₁ (inj₁ j) = inj₁ (inj₁ (InThereNat _ j _ _)) -- inj₁ (inj₁ (InThere γ j m b'))
decidInLConNat (addₗ m b' γ) t | inj₂ k | inj₁ (inj₂ j) = inj₁ (inj₂ (InThereNat _ j _ _)) -- inj₁ (inj₂ (InThere γ j m b'))
decidInLConNat (addₗ m b γ) t | inj₂ k | inj₂ j = inj₂ (NotInThereNat _ j _ _ (DifferentDifferentNat _ _ λ e → k (PE.sym e))) -- inj₂ (NotInThere γ j m b k)


BackNotInLConNat≤ : ∀ {m l l'} (≤ε : l ≤ₗ l') → NotInLConNat m l' → NotInLConNat m l
BackNotInLConNat≤ {m = m} {l = l} f< notinl' with  decidInLConNat l m
BackNotInLConNat≤ {m = m} {l = l} f< notinl' | inj₁ (inj₁ inl) =
  PE.⊥-elim (NotInLConNotInLCon {n = 0} _ _ _ (NotInLConNatNotInLCon _ _ _ notinl' PE.refl) (f< _ _ (InLConNatInLCon inl)))
BackNotInLConNat≤ {m = m} {l = l} f< notinl' | inj₁ (inj₂ inl) = 
  PE.⊥-elim (NotInLConNotInLCon {n = 0} _ _ _ (NotInLConNatNotInLCon _ _ _ notinl' PE.refl) (f< _ _ (InLConNatInLCon inl)))
BackNotInLConNat≤ {m = m} {l = l} f< notinl' | inj₂ notinl = notinl


InLConTrueNat : ∀ {n} (t : Term n) b l → InLCon t b l → TrueNat t
InLConTrueNat _ _ _ (InHere t b t=m u=b l) rewrite t=m = TrueNatToTerm _ t
InLConTrueNat t b (addₗ t2 b2 l) (InThere _ tε t2 b2) = InLConTrueNat t b l tε

InLConTrueBool : ∀ {n} (t : Term n) b l → InLCon t b l → TrueBool b
InLConTrueBool _ _ _ (InHere t b t=m u=b l) rewrite u=b = TrueBboolToTerm _ b
InLConTrueBool t b (addₗ t2 b2 l) (InThere _ tε t2 b2) = InLConTrueBool t b l tε

InLConUnique : ∀ {n} (t b b' : Term n) l (lε : ⊢ₗ l) → InLCon t b l → InLCon t b' l → b PE.≡ b'
InLConUnique t b b' εₗ ⊢ₗₑ () ()
InLConUnique t u u' (addₗ n b l) (⊢ₗ• l lε n b nbε) (InHere n b t=n u=b l) (InHere n b t=n' u=b' l) = PE.trans u=b (PE.sym u=b')
InLConUnique t u u' (addₗ n b l) (⊢ₗ• l lε n b nbε) (InHere n b t=n u=b l) (InThere _ inl n b) = PE.⊥-elim (NotInLConNotInLCon _ _ _ (NotInLConNatNotInLCon _ _ _ nbε t=n) inl)
InLConUnique t u u' (addₗ n b l) (⊢ₗ• l lε n b nbε) (InThere _ inl n b) (InHere n b t=n u=b l) = PE.⊥-elim (NotInLConNotInLCon _ _ _ (NotInLConNatNotInLCon _ _ _ nbε t=n) inl)
InLConUnique t u u' (addₗ n b l) (⊢ₗ• l lε n b nbε) (InThere _ inl n b) (InThere _ inl' n b) = InLConUnique _ _ _ l lε inl inl'

-- InLConUnique .(natToTerm _ n) .(BboolToTerm _ Btrue) false _ (⊢ₗ• l lε n Btrue nbε) (InHere n Btrue l) (InThere _ false l inl' _ _) = PE.⊥-elim (NotInLConNotInLCon _ _ l (NotInLConNatNotInLCon _ _ l nbε PE.refl) inl')
--InLConUnique t b b' (addₗ n b₁ γ) (⊢ₗ• .γ lε .n .b₁ nbε)
--    (InThere .t .b .γ x .n .b₁)
--    (InThere .t .b' .γ x₁ .n .b₁) = ?
--findBoolLCon : ∀ {n : Nat} (t : Term n) (γ : LCon) → InLCon t γ → Bbool
--findBoolLCon _ _ (InHere t γ b) = b
--findBoolLCon _ _ (InThere t tε γ γε m b) = findBoolLCon _ γ γε

permutInLCon : ∀ {n : Nat} (m : Nat) (l : LCon) (t b : Term n)
               → InLCon t b l
               → InLCon t b (permut m l)
permutInLCon 0 (addₗ t b εₗ) _ _ (InHere t b t=m u=b εₗ) = InHere t b t=m u=b εₗ       
permutInLCon 0 (addₗ t b (addₗ t2 b2 l)) _ _ (InHere m b t=m u=b .(addₗ t2 b2 l)) = InThere _ (InHere m b t=m u=b l) t2 b2
permutInLCon 0 (addₗ x x₁ (addₗ m b l)) t u (InThere .(addₗ m b l) (InHere m b t=m u=b l) .x .x₁) = InHere m b t=m u=b (addₗ x x₁ _)
permutInLCon 0 (addₗ x x₁ (addₗ x₂ x₃ l)) t _ (InThere .(addₗ x₂ x₃ l) (InThere .l x₄ .x₂ .x₃) .x .x₁) = InThere _ (InThere _ x₄ _ _) _ _
permutInLCon (1+ m) (addₗ t b εₗ) _ _ (InHere t b t=m u=b .εₗ) = InHere t b t=m u=b εₗ
permutInLCon (1+ m) (addₗ x x₁ l) t _ (InThere .l x₂ .x .x₁) = InThere (permut _ l) (permutInLCon _ _ _ _ x₂) _ _
permutInLCon (1+ m) (addₗ x x₁ (addₗ x₂ x₃ l)) .(natToTerm _ x) _ (InHere .x .x₁ PE.refl PE.refl .(addₗ x₂ x₃ l)) = InHere x _ PE.refl PE.refl _

permutNotInLCon : ∀ {n} (m : Nat) (l : LCon) (t : Term n)
               → NotInLCon t l
               → NotInLCon t (permut m l)
permutNotInLCon 0 εₗ _ tε = tε 
permutNotInLCon 0 (addₗ m b εₗ) _ tε = tε
permutNotInLCon 0 (addₗ n b (addₗ m b' l)) t (NotInThere _ (NotInThere l lε m b' neqm) n b neqn) = NotInThere _ (NotInThere _ lε n b neqn) m b' neqm
permutNotInLCon (1+ m) εₗ t tε = tε
permutNotInLCon (1+ m) (addₗ k b l) t (NotInThere l lε k b neqk) = NotInThere _ (permutNotInLCon m l t lε) k b neqk



permutNotInLConNat : ∀ (m : Nat) (l : LCon) (t : Nat)
               → NotInLConNat t l
               → NotInLConNat t (permut m l)
permutNotInLConNat 0 εₗ _ tε = tε 
permutNotInLConNat 0 (addₗ t b εₗ) _ tε = tε
permutNotInLConNat 0 (addₗ n b (addₗ m b' l)) t (NotInThereNat _ (NotInThereNat l lε m b' neqm) n b neqn) = NotInThereNat _ (NotInThereNat _ lε n b neqn) m b' neqm
permutNotInLConNat (1+ m) εₗ t tε = tε
permutNotInLConNat (1+ m) (addₗ k b l) t (NotInThereNat l lε k b neqk) = NotInThereNat _ (permutNotInLConNat m l t lε) k b neqk

permutε : ∀ (n : Nat) {l : LCon} (lε : ⊢ₗ l)
            → ⊢ₗ (permut n l)
permutε n ⊢ₗₑ = ⊢ₗₑ
permutε 0 (⊢ₗ• εₗ ⊢ₗₑ m b mbε) = ⊢ₗ• εₗ ⊢ₗₑ m b mbε
permutε 0 (⊢ₗ• _ (⊢ₗ• γ γε m b mbε) m' b' (NotInThereNat _ mbε' _ _ neq)) = ⊢ₗ• _ (⊢ₗ• _ γε m' b' mbε') m b (NotInThereNat _ mbε _ _ (DifferentNatSym m' m neq))
permutε (1+ n) (⊢ₗ• γ γε m b mbε) =  ⊢ₗ• _ (permutε n γε) m b (permutNotInLConNat n γ m mbε)

--permutfindBoolLCon : ∀ {n : Nat} (m : Nat) (l : LCon) (t : Term n)
--               → (tε : InLCon t l)
--               → findBoolLCon t l tε PE.≡ findBoolLCon t (permut m l) (permutInLCon m l t tε)
--permutfindBoolLCon 0 l t tε = {!!}
--permutfindBoolLCon (1+ m) l t tε = {!!}

-- Neutral terms.


-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.

mutual 
  data Neutral : Term n → Set where
    var       : (x : Fin n) → Neutral (var x)
    ∘ₙ        : Neutral t   → Neutral (t ∘ u)
    fstₙ      : Neutral t   → Neutral (fst t)
    sndₙ      : Neutral t   → Neutral (snd t)
    natrecₙ   : Neutral v   → Neutral (natrec G t u v)
    boolrecₙ   : Neutral v   → Neutral (boolrec G t u v)
--    Emptyrecₙ : Neutral t   → Neutral (Emptyrec A t)
    -- α t is a neutral if t is recursively a neutral (i.e. Suc (Suc (Suc x)) is a neutral)
    αₙ        : ContainsNeutral t → Neutral (α t)

  data ContainsNeutral : Term n → Set where
    ncontn    : Neutral t → ContainsNeutral t
    Scontn    : ContainsNeutral t → ContainsNeutral (suc t)


data αNeutral {l : LCon} : ∀ (m : Nat) → Term n → Set where
  αₙ-base   : ∀ (m : Nat) {t : Term n} → t PE.≡ natToTerm _ m → NotInLConNat m l → αNeutral m (α t)
  ∘ₙ        : ∀ {m} → αNeutral {l} m t   → αNeutral m (t ∘ u)
  fstₙ      : ∀ {m} → αNeutral {l} m t   → αNeutral m (fst t)
  sndₙ      : ∀ {m} → αNeutral {l} m t   → αNeutral m (snd t)
  natrecₙ   : ∀ {m} → αNeutral {l} m v   → αNeutral m (natrec G t u v)
  boolrecₙ  : ∀ {m} → αNeutral {l} m v   → αNeutral m (boolrec G t u v)
--  Emptyrecₙ : ∀ {m} → αNeutral {l} {lε} m t   → αNeutral m (Emptyrec A t)
  αₙ-rec    : ∀ {m} → αNeutral {l} m t   → αNeutral m (α t)

BackταNeutral : ∀ {l : LCon} {m n b} → αNeutral {addₗ n b l} m t → αNeutral {l} m t
BackταNeutral (αₙ-base m tε (NotInThereNat l notinl n b t≠n)) = αₙ-base m tε notinl
BackταNeutral (αₙ-rec tε) = αₙ-rec (BackταNeutral tε)
BackταNeutral (∘ₙ d) = ∘ₙ (BackταNeutral d)
BackταNeutral (fstₙ d) = fstₙ (BackταNeutral d)
BackταNeutral (sndₙ d) = sndₙ (BackταNeutral d)
BackταNeutral (natrecₙ d) = natrecₙ (BackταNeutral d)
BackταNeutral (boolrecₙ d) = boolrecₙ (BackταNeutral d)
-- BackταNeutral (Emptyrecₙ d) = Emptyrecₙ (BackταNeutral d)

αNeNotIn : ∀ {l l' m} {t : Term n} → NotInLConNat m l' → αNeutral {l} m t → αNeutral {l'} m t
αNeNotIn notl' (αₙ-base m e notl) = αₙ-base m e notl'
αNeNotIn notl' (αₙ-rec tε) = αₙ-rec (αNeNotIn notl' tε)
αNeNotIn notl' (∘ₙ d) = ∘ₙ (αNeNotIn notl' d)
αNeNotIn notl' (fstₙ d) = fstₙ (αNeNotIn notl' d)
αNeNotIn notl' (sndₙ d) = sndₙ (αNeNotIn notl' d)
αNeNotIn notl' (natrecₙ d) = natrecₙ (αNeNotIn notl' d)
αNeNotIn notl' (boolrecₙ d) = boolrecₙ (αNeNotIn notl' d)
-- αNeNotIn notl' (Emptyrecₙ d) = Emptyrecₙ (αNeNotIn notl' d)

NoTrueNatNe : ∀ (t : Term n) → TrueNat t → Neutral t → PE.⊥
NoTrueNatNe _ (Truesuc tε) ()

NoTrueNatConNe : ∀ (t : Term n) → TrueNat t → ContainsNeutral t → PE.⊥
NoTrueNatConNe _ (Truesuc tε) (Scontn tcontn) = NoTrueNatConNe _ tε tcontn
NoTrueNatConNe _ tε (ncontn net) = NoTrueNatNe _ tε net

NoTrueNatαNe : ∀ {l : LCon} {m} → (t : Term n) → TrueNat t → αNeutral {l} m t → PE.⊥
NoTrueNatαNe _ (Truesuc tε) () -- = {!!}


-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {l : LCon} {n : Nat} : Term n → Set where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  Πₙ     : Whnf (Π A ▹ B)
  Σₙ     : Whnf (Σ A ▹ B)
  ℕₙ     : Whnf ℕ
  𝔹ₙ     : Whnf 𝔹
--   Unitₙ  : Whnf Unit
--   Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc t)
--   starₙ : Whnf star
  trueₙ : Whnf true
  falseₙ : Whnf false
  prodₙ : Whnf (prod t u)

  -- Neutrals are whnfs.
  ne    : Neutral t → Whnf t

  -- α's are whnfs if their argument is not in the list l. Otherwise it will reduce.
  αₙ : ∀ {m} → αNeutral {l} m t → Whnf t


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : Neutral A → U PE.≢ A
U≢ne () PE.refl

U≢αne : ∀ {l : LCon} {m} → αNeutral {l} m A → U PE.≢ A
U≢αne () PE.refl

ℕ≢ne : Neutral A → ℕ PE.≢ A
ℕ≢ne () PE.refl

ℕ≢αne : ∀ {l : LCon} {m} → αNeutral {l} m A → ℕ PE.≢ A
ℕ≢αne () PE.refl

𝔹≢ne : Neutral A → 𝔹 PE.≢ A
𝔹≢ne () PE.refl

𝔹≢αne : ∀ {l : LCon} {m} → αNeutral {l} m A → 𝔹 PE.≢ A
𝔹≢αne () PE.refl

-- Empty≢ne : Neutral A → Empty PE.≢ A
-- Empty≢ne () PE.refl

-- Empty≢αne : ∀ {l : LCon} {lε : ⊢ₗ l} {m} → αNeutral {l} {lε} m A → Empty PE.≢ A
-- Empty≢αne () PE.refl

-- Unit≢ne : Neutral A → Unit PE.≢ A
-- Unit≢ne () PE.refl
 
-- Unit≢αne : ∀ {l : LCon} {lε : ⊢ₗ l} {m} → αNeutral {l} {lε} m A → Unit PE.≢ A
-- Unit≢αne () PE.refl

mutual 
  ne≢αne : ∀ {n m : Nat} {A B : Term n} {l : LCon} → Neutral A → αNeutral {l} m B → A PE.≢ B
  ne≢αne (αₙ contn) (αₙ-base m e tε) PE.refl rewrite e = NoTrueNatConNe _ (TrueNatToTerm _ m) contn
  ne≢αne (αₙ contn) (αₙ-rec tε) PE.refl = conne≢αne contn tε PE.refl
  ne≢αne (∘ₙ net) (∘ₙ αnet) PE.refl = ne≢αne net αnet PE.refl
  ne≢αne (fstₙ net) (fstₙ αnet) PE.refl = ne≢αne net αnet PE.refl
  ne≢αne (sndₙ net) (sndₙ αnet) PE.refl = ne≢αne net αnet PE.refl
  ne≢αne (natrecₙ net) (natrecₙ αnet) PE.refl = ne≢αne net αnet PE.refl
  ne≢αne (boolrecₙ net) (boolrecₙ αnet) PE.refl = ne≢αne net αnet PE.refl
--  ne≢αne (Emptyrecₙ net) (Emptyrecₙ αnet) PE.refl = ne≢αne net αnet PE.refl
  
  conne≢αne : ∀ {n m} {A B : Term n} {l : LCon} → ContainsNeutral A → αNeutral {l} m B → A PE.≢ B
  conne≢αne (ncontn net) αt = ne≢αne net αt
  conne≢αne (Scontn contn) () PE.refl

B≢ne : ∀ W → Neutral A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

B≢αne : ∀ {l m} W → αNeutral {l} m A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢αne BΠ () PE.refl
B≢αne BΣ () PE.refl

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

𝔹≢B : ∀ W → 𝔹 PE.≢ ⟦ W ⟧ F ▹ G
𝔹≢B BΠ ()
𝔹≢B BΣ ()

-- Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
-- Empty≢B BΠ ()
-- Empty≢B BΣ ()

-- Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
-- Unit≢B BΠ ()
-- Unit≢B BΣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne () PE.refl

true≢ne : Neutral t → true PE.≢ t
true≢ne () PE.refl

false≢ne : Neutral t → false PE.≢ t
false≢ne () PE.refl

TrueNat≢Cne : ContainsNeutral t → TrueNat t → PE.⊥
TrueNat≢Cne (ncontn tε) (Truezero) = zero≢ne tε PE.refl
TrueNat≢Cne (Scontn tε) (Truesuc kε) = TrueNat≢Cne tε kε

TrueNat≢U : TrueNat {n} U → PE.⊥
TrueNat≢U ()

TrueBool≢U : TrueBool {n} U → PE.⊥
TrueBool≢U ()

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} {l} : Term n → Set where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral t → Natural t
  neα   : ∀ {m} → αNeutral {l} m t → Natural t


-- A whnf of type 𝔹 is either true, false, or neutral.

data Boolean {n : Nat} {l} : Term n → Set where
  trueₙ :             Boolean true
  falseₙ  :           Boolean false
  ne    : Neutral t → Boolean t
  neα   : ∀ {m} → αNeutral {l} m t → Boolean t

-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {n : Nat} {l : LCon} : Term n → Set where
  Πₙ     :             Type (Π A ▹ B)
  Σₙ     :             Type (Σ A ▹ B)
  ℕₙ     :             Type ℕ
  𝔹ₙ     :             Type 𝔹
--  Emptyₙ :             Type Empty
--  Unitₙ  :             Type Unit
  ne     : Neutral t → Type t
  αne   : ∀ {m} → αNeutral {l} m t → Type t

⟦_⟧-type : ∀ {l} (W : BindingType) → Type {_} {l} (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {n : Nat} {l} : Term n → Set where
  lamₙ : Function (lam t)
  ne   : Neutral t → Function t
  neα : ∀ {m} → αNeutral {l} m t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {n : Nat} {l} : Term n → Set where
  prodₙ : Product (prod t u)
  ne    : Neutral t → Product t
  neα : ∀ {m} → αNeutral {l} m t → Product t

-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

TrueNatNatural : ∀ {l} → TrueNat t → Natural {_} {l} t
TrueNatNatural Truezero = zeroₙ
TrueNatNatural (Truesuc tε) = sucₙ

naturalWhnf : ∀ {l : LCon} → Natural {_} {l} t → Whnf {l} t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne x) = ne x
naturalWhnf (neα x) = αₙ x

booleanWhnf : ∀ {l : LCon} → Boolean {_} {l} t → Whnf {l} t
booleanWhnf trueₙ   = trueₙ
booleanWhnf falseₙ  = falseₙ
booleanWhnf (ne x) = ne x
booleanWhnf (neα x) = αₙ x

typeWhnf : ∀ {l : LCon} → Type {_} {l} A → Whnf {l} A
typeWhnf Πₙ     = Πₙ
typeWhnf Σₙ     = Σₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf 𝔹ₙ     = 𝔹ₙ
-- typeWhnf Emptyₙ = Emptyₙ
-- typeWhnf Unitₙ  = Unitₙ
typeWhnf (ne x) = ne x
typeWhnf (αne x) = αₙ x

functionWhnf : ∀ {l : LCon} → Function {_} {l} t → Whnf {l} t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne x) = ne x
functionWhnf (neα x) = αₙ x

productWhnf : ∀ {l : LCon} → Product {_} {l} t → Whnf {l} t
productWhnf prodₙ  = prodₙ
productWhnf (ne x) = ne x
productWhnf (neα x) = αₙ x

⟦_⟧ₙ : ∀ {l : LCon} → (W : BindingType) → Whnf {l} (⟦ W ⟧ F ▹ G)
⟦_⟧ₙ BΠ = Πₙ
⟦_⟧ₙ BΣ = Σₙ


------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Nat → Nat → Set where
  id    : {n : Nat} → Wk n n                      -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  {l m n : Nat} → Wk l m → Wk m n → Wk l n
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

liftn : {k m : Nat} → Wk k m → (n : Nat) → Wk (n + k) (n + m)
liftn ρ Nat.zero = ρ
liftn ρ (1+ n)   = lift (liftn ρ n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar η x ∈ dom(Γ).

wkVar : {m n : Nat} (ρ : Wk m n) (x : Fin n) → Fin m
wkVar id x            = x
wkVar (step ρ) x      = (wkVar ρ x) +1
wkVar (lift ρ) x0     = x0
wkVar (lift ρ) (x +1) = (wkVar ρ x) +1

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n) (c : GenTs Term n bs) → GenTs Term m bs
  wkGen ρ []                = []
  wkGen ρ (_∷_ {b = b} t c) = (wk (liftn ρ b) t) ∷ (wkGen ρ c)

  wk : {m n : Nat} (ρ : Wk m n) (t : Term n) → Term m
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen k c) = gen k (wkGen ρ c)


-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term n → Term (1+ n)
wk1 = wk (step id)

-- Weakening of a neutral term.
mutual
  wkNeutral : ∀ ρ → Neutral t → Neutral {n} (wk ρ t)
  wkNeutral ρ (var n)       = var (wkVar ρ n)
  wkNeutral ρ (∘ₙ n)        = ∘ₙ (wkNeutral ρ n)
  wkNeutral ρ (fstₙ n)      = fstₙ (wkNeutral ρ n)
  wkNeutral ρ (sndₙ n)      = sndₙ (wkNeutral ρ n)
  wkNeutral ρ (natrecₙ n)   = natrecₙ (wkNeutral ρ n)
  wkNeutral ρ (boolrecₙ n)   = boolrecₙ (wkNeutral ρ n)
--  wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)
  wkNeutral ρ (αₙ e) = αₙ (wkContainsNeutral ρ e)

  wkContainsNeutral : ∀ ρ → ContainsNeutral t → ContainsNeutral {n} (wk ρ t)
  wkContainsNeutral ρ (ncontn t) = ncontn (wkNeutral ρ t)
  wkContainsNeutral ρ (Scontn t) = Scontn (wkContainsNeutral ρ t)

wkTrueNat : ∀ ρ → TrueNat t → TrueNat {n} (wk ρ t)
wkTrueNat ρ Truezero = Truezero
wkTrueNat ρ (Truesuc tε) = Truesuc (wkTrueNat _ tε)

wkNatToTerm :  ∀ {n m } (ρ : Wk m n) (t : Nat) →  wk ρ (natToTerm n t) PE.≡ natToTerm m t
wkNatToTerm ρ Nat.zero = PE.refl
wkNatToTerm ρ (1+ t) rewrite (wkNatToTerm ρ t) = PE.refl

wkDifferentTrueNat : ∀ {n m } (ρ : Wk m n) (t u : Term n) → DifferentTrueNat t u → DifferentTrueNat {m} (wk ρ t) (wk ρ u)
wkDifferentTrueNat ρ _ _ (Diff0rTrueNat _ tε) = Diff0rTrueNat _ (wkTrueNat _ tε)
wkDifferentTrueNat ρ _ _ (Diff0lTrueNat _ tε) = Diff0lTrueNat _ (wkTrueNat _ tε)
wkDifferentTrueNat ρ _ _ (DiffSucTrueNat _ _ e) = DiffSucTrueNat _ _ (wkDifferentTrueNat ρ _ _ e)


wkNotInLCon : ∀ l ρ → NotInLCon t l → NotInLCon {n} (wk ρ t) l 
wkNotInLCon _ ρ (NotInε tε) = NotInε (wkTrueNat _ tε)
wkNotInLCon (addₗ m b γ) ρ (NotInThere .γ γε .m .b e) = NotInThere γ (wkNotInLCon _ _ γε) m b (PE.subst (λ h → DifferentTrueNat _ h) ((wkNatToTerm ρ m)) (wkDifferentTrueNat ρ _ _ e))

αwkNeutral : ∀ {l m} ρ → αNeutral {l} m t → αNeutral {l} {n} m (wk ρ t)
αwkNeutral ρ (αₙ-base m e notn) rewrite e = αₙ-base m (wkNatToTerm ρ m) notn
αwkNeutral ρ (αₙ-rec n)       = αₙ-rec (αwkNeutral _ n)
αwkNeutral  ρ (∘ₙ n)        = ∘ₙ (αwkNeutral ρ n)
αwkNeutral ρ (fstₙ n)      = fstₙ (αwkNeutral ρ n)
αwkNeutral ρ (sndₙ n)      = sndₙ (αwkNeutral ρ n)
αwkNeutral ρ (natrecₙ n)   = natrecₙ (αwkNeutral ρ n)
αwkNeutral ρ (boolrecₙ n)   = boolrecₙ (αwkNeutral ρ n)
-- αwkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (αwkNeutral ρ e)

αNeutralHProp : ∀ {l m m'} → αNeutral {l} m t → αNeutral {l} m' t → m PE.≡ m'
αNeutralHProp (αₙ-base m e notn) (αₙ-base m' e' notn') rewrite e rewrite e' = EqNatToTermEqNat _ _ e'
αNeutralHProp (αₙ-rec n) (αₙ-rec m)       = αNeutralHProp n m
αNeutralHProp (∘ₙ n) (∘ₙ m)        = αNeutralHProp n m
αNeutralHProp (fstₙ n) (fstₙ m)      = αNeutralHProp n m
αNeutralHProp (sndₙ n) (sndₙ m)      = αNeutralHProp n m
αNeutralHProp (natrecₙ n) (natrecₙ m)   = αNeutralHProp n m
αNeutralHProp (boolrecₙ n) (boolrecₙ m)   = αNeutralHProp n m
-- αNeutralHProp (Emptyrecₙ n) (Emptyrecₙ m) = αNeutralHProp n m
αNeutralHProp (αₙ-base n e notn) (αₙ-rec m) rewrite e = PE.⊥-elim (NoTrueNatαNe _ (TrueNatToTerm _ n) m)
αNeutralHProp (αₙ-rec m) (αₙ-base n e notn) rewrite e = PE.⊥-elim (NoTrueNatαNe _ (TrueNatToTerm _ n) m)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ {l} → Natural  {_} {l} t → Natural {n} {l} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)
wkNatural ρ (neα x) = neα (αwkNeutral ρ x)

wkBoolean : ∀ {l} ρ → Boolean  {_} {l} t → Boolean {n} {l} (wk ρ t)
wkBoolean ρ trueₙ   = trueₙ
wkBoolean ρ falseₙ  = falseₙ
wkBoolean ρ (ne x) = ne (wkNeutral ρ x)
wkBoolean ρ (neα x) = neα (αwkNeutral ρ x)

wkType : ∀ {l} ρ → Type {_} {l} t → Type {n} {l} (wk ρ t)
wkType ρ Πₙ     = Πₙ
wkType ρ Σₙ     = Σₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ 𝔹ₙ     = 𝔹ₙ
-- wkType ρ Emptyₙ = Emptyₙ
-- wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)
wkType ρ (αne x) = αne (αwkNeutral ρ x)

wkFunction : ∀ {l} ρ → Function {_} {l} t → Function {n} {l} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)
wkFunction ρ (neα x) = neα (αwkNeutral ρ x)


wkProduct : ∀ {l} ρ → Product {_} {l} t → Product {n} {l} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)
wkProduct ρ (neα x) = neα (αwkNeutral ρ x)

wkBboolToTerm :  ∀ {n m } (ρ : Wk m n) (b : Bbool) →  wk ρ (BboolToTerm n b) PE.≡ BboolToTerm m b
wkBboolToTerm ρ Btrue = PE.refl
wkBboolToTerm ρ Bfalse = PE.refl

wkInLCon : ∀ l ρ → InLCon t b l → InLCon {n} (wk ρ t) (wk ρ b) l 
wkInLCon _ ρ (InHere t b t=m u=b l) rewrite  t=m rewrite u=b rewrite (wkBboolToTerm ρ b) rewrite (wkNatToTerm ρ t) = InHere _ _ PE.refl PE.refl l -- InHere t b l
wkInLCon _ ρ (InThere l tbε t2 b2) = InThere l (wkInLCon l ρ tbε) t2 b2


wkWhnf : ∀ {l} ρ → Whnf {l} t → Whnf {l} {n} (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Σₙ      = Σₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ 𝔹ₙ      = 𝔹ₙ
-- wkWhnf ρ Emptyₙ  = Emptyₙ
-- wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ trueₙ   = trueₙ
wkWhnf ρ falseₙ   = falseₙ
-- wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)
wkWhnf ρ (αₙ tε) = αₙ (αwkNeutral ρ tε)

-- Non-dependent version of Π.

_▹▹_ : Term n → Term n → Term n
A ▹▹ B = Π A ▹ wk1 B

-- Non-dependent products.

_××_ : Term n → Term n → Term n
A ×× B = Σ A ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Nat → Nat → Set
Subst m n = Fin n → Term m

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst m (1+ n) → Term m
head σ = σ x0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst m (1+ n) → Subst m n
tail σ x = σ (x +1)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst m n) (x : Fin n) → Term m
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst n n
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst m n → Subst (1+ m) n
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst m n) → Subst (1+ m) (1+ n)
liftSubst σ x0     = var x0
liftSubst σ (x +1) = wk1Subst σ x

liftSubstn : {k m : Nat} → Subst k m → (n : Nat) → Subst (n + k) (n + m)
liftSubstn σ Nat.zero = σ
liftSubstn σ (1+ n)   = liftSubst (liftSubstn σ n)

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst :  Wk m n → Subst m n
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : {bs : List Nat} (σ : Subst m n) (g : GenTs Term n bs) → GenTs Term m bs
  substGen σ  []      = []
  substGen σ (_∷_ {b = b} t ts) = subst (liftSubstn σ b) t ∷ (substGen σ ts)

  subst : (σ : Subst m n) (t : Term n) → Term m
  subst σ (var x)   = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst m n → Term m → Subst m (1+ n)
consSubst σ t  x0    = t
consSubst σ t (x +1) = σ x

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term n → Subst n (1+ n)
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst ℓ m → Subst m n → Subst ℓ n
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk ℓ m → Subst m n → Subst ℓ n
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst ℓ m → Wk m n → Subst ℓ n
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term (1+ n)) (s : Term n) → Term n
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term (1+ n)) (s : Term (1+ n)) → Term (1+ n)
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t


B-subst : (σ : Subst m n) (W : BindingType) (F : Term n) (G : Term (1+ n))
        → subst σ (⟦ W ⟧ F ▹ G) PE.≡ ⟦ W ⟧ (subst σ F) ▹ (subst (liftSubst σ) G)
B-subst σ BΠ F G = PE.refl
B-subst σ BΣ F G = PE.refl
