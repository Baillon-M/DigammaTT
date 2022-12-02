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

  Unitkind : Kind []
  Starkind : Kind []

  Emptykind    : Kind []
  Emptyreckind : Kind (0 ∷ 0 ∷ [])

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

Empty : Term n                       -- Empty type
Empty = gen Emptykind []

Unit  : Term n                       -- Unit type
Unit = gen Unitkind []

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

star : Term n                        -- Unit element
star = gen Starkind []

Emptyrec : (A e : Term n) → Term n   -- Empty type recursor
Emptyrec A e = gen Emptyreckind (A ∷ e ∷ [])

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


data InLCon : ∀ {n : Nat} (t : Term n) (b : Term n) → LCon → Set
  where
    InHere :  ∀ {n : Nat} (t : Nat) (b : Bbool) (γ : LCon) → InLCon (natToTerm n t) (BboolToTerm n b) (addₗ t b γ)
    InThere :  ∀ {n : Nat} (t b : Term n) (γ : LCon) (γε : InLCon t b γ) (m : Nat) (b' : Bbool) → InLCon t b (addₗ m b' γ)

data DifferentNat {n : Nat} : ∀ (t u : Term n) → Set where
  Diff0r : ∀ (t : Term n) (tε : TrueNat t) → DifferentNat (suc t) zero
  Diff0l : ∀ (t : Term n) (tε : TrueNat t) → DifferentNat zero (suc t)
  DiffSuc : ∀ (t u : Term n) → DifferentNat t u → DifferentNat (suc t) (suc u)
  
                
data NotInLCon {n : Nat} (t : Term n) : LCon → Set
  where
    NotInε : TrueNat t → NotInLCon t εₗ 
    NotInThere : ∀ (γ : LCon) (γε : NotInLCon t γ) (m : Nat) (b : Bbool) → DifferentNat t (natToTerm n m) → NotInLCon t (addₗ m b γ)



decidEqNat :  ∀ (t u : Term n) (tε : TrueNat t) (uε : TrueNat u) → (t PE.≡ u) ⊎ (DifferentNat t u)
decidEqNat zero zero Truezero Truezero = inj₁ PE.refl
decidEqNat .(suc _) .zero (Truesuc tε) Truezero = inj₂ (Diff0r _ tε)
decidEqNat zero .(suc _) Truezero (Truesuc uε) = inj₂ (Diff0l _ uε)
decidEqNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε)
  with decidEqNat _ _ tε uε
decidEqNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) | inj₁ k rewrite k = inj₁ PE.refl
decidEqNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) | inj₂ k = inj₂ (DiffSuc _ _ k)

EqNatEqTrueNat : ∀ (t u : Term n) (tε : TrueNat t) (uε : TrueNat u) (e : t PE.≡ u) → (PE.subst TrueNat e tε PE.≡ uε)
EqNatEqTrueNat zero zero Truezero Truezero PE.refl = PE.refl
EqNatEqTrueNat .(suc _) .(suc _) (Truesuc tε) (Truesuc uε) PE.refl = PE.cong Truesuc (EqNatEqTrueNat _ _ tε uε PE.refl)

decidInLCon : ∀ (γ : LCon) (t : Term n) (tε : TrueNat t) → (∃ (λ b → InLCon t b γ)) ⊎ (NotInLCon t γ)
decidInLCon εₗ t tε = inj₂ (NotInε tε)
decidInLCon (addₗ m b γ) t tε with decidEqNat _ _ tε (TrueNatToTerm _ m)
decidInLCon (addₗ m b γ) t tε | inj₁ k rewrite k rewrite (PE.sym (EqNatEqTrueNat _ _ (TrueNatToTerm _ m) tε PE.refl)) = inj₁ ((BboolToTerm _ b) , InHere m b γ)
decidInLCon (addₗ m b γ) t tε | inj₂ k with decidInLCon γ t tε
decidInLCon (addₗ m b' γ) t tε | inj₂ k | inj₁ (b , j) = inj₁ (b , InThere t b γ j m b')
decidInLCon (addₗ m b γ) t tε | inj₂ k | inj₂ j = inj₂ (NotInThere γ j m b k)

InLConTrueNat : ∀ {n} (t : Term n) b l → InLCon t b l → TrueNat t
InLConTrueNat _ _ _ (InHere t b l) = TrueNatToTerm _ t
InLConTrueNat t b (addₗ t2 b2 l) (InThere _ _ _ tε t2 b2) = InLConTrueNat t b l tε

InLConTrueBool : ∀ {n} (t : Term n) b l → InLCon t b l → TrueBool b
InLConTrueBool _ _ _ (InHere t b l) = TrueBboolToTerm _ b
InLConTrueBool t b (addₗ t2 b2 l) (InThere _ _ _ tε t2 b2) = InLConTrueBool t b l tε

--findBoolLCon : ∀ {n : Nat} (t : Term n) (γ : LCon) → InLCon t γ → Bbool
--findBoolLCon _ _ (InHere t γ b) = b
--findBoolLCon _ _ (InThere t tε γ γε m b) = findBoolLCon _ γ γε

permut : ∀ (n : Nat) (l : LCon) → LCon
permut n εₗ = εₗ
permut 0 (addₗ n2 b2 εₗ) = addₗ n2 b2 εₗ
permut 0 (addₗ n1 b1 (addₗ n2 b2 l)) = (addₗ n2 b2 (addₗ n1 b1 l))
permut (1+ n) (addₗ n1 b1 l) = addₗ n1 b1 (permut n l)

permutInLCon : ∀ {n : Nat} (m : Nat) (l : LCon) (t b : Term n)
               → InLCon t b l
               → InLCon t b (permut m l)
permutInLCon 0 (addₗ t b εₗ) _ _ (InHere t b εₗ) = InHere t b εₗ       
permutInLCon 0 (addₗ t b (addₗ t2 b2 l)) _ _ (InHere t b .(addₗ t2 b2 l)) = InThere _ _ _ (InHere t b l) t2 b2
permutInLCon 0 (addₗ x x₁ (addₗ t b l)) _ _ (InThere _ _ .(addₗ t b l) (InHere t b l) .x .x₁) = InHere t b _
permutInLCon 0 (addₗ x x₁ (addₗ x₂ x₃ l)) t _ (InThere .t _ .(addₗ x₂ x₃ l) (InThere .t _ .l x₄ .x₂ .x₃) .x .x₁) = InThere _ _ _ (InThere _ _ _ x₄ _ _) _ _
permutInLCon (1+ m) (addₗ t b εₗ) _ _ (InHere t b .εₗ) = InHere t b εₗ
permutInLCon (1+ m) (addₗ x x₁ l) t _ (InThere .t _ .l x₂ .x .x₁) = InThere _ _ (permut _ l) (permutInLCon _ _ _ _ x₂) _ _
permutInLCon (1+ m) (addₗ x x₁ (addₗ x₂ x₃ l)) .(natToTerm _ x) _ (InHere .x .x₁ .(addₗ x₂ x₃ l)) = InHere x _ _

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
    Emptyrecₙ : Neutral t   → Neutral (Emptyrec A t)
    -- α t is a neutral if t is recursively a neutral (i.e. Suc (Suc (Suc x)) is a neutral)
    αₙ        : ContainsNeutral t → Neutral (α t)

  data ContainsNeutral : Term n → Set where
    ncontn    : Neutral t → ContainsNeutral t
    Scontn    : ContainsNeutral t → ContainsNeutral (suc t)



-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Whnf {l : LCon} {n : Nat} : Term n → Set where

  -- Type constructors are whnfs.
  Uₙ     : Whnf U
  Πₙ     : Whnf (Π A ▹ B)
  Σₙ     : Whnf (Σ A ▹ B)
  ℕₙ     : Whnf ℕ
  𝔹ₙ     : Whnf 𝔹
  Unitₙ  : Whnf Unit
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : Whnf (lam t)
  zeroₙ : Whnf zero
  sucₙ  : Whnf (suc t)
  starₙ : Whnf star
  trueₙ : Whnf true
  falseₙ : Whnf false
  prodₙ : Whnf (prod t u)

  -- Neutrals are whnfs.
  ne    : Neutral t → Whnf t

  -- α's are whnfs if their argument is not in the list l. Otherwise it will reduce.
  αₙ : NotInLCon t l → Whnf (α t)


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ne : Neutral A → U PE.≢ A
U≢ne () PE.refl

ℕ≢ne : Neutral A → ℕ PE.≢ A
ℕ≢ne () PE.refl

𝔹≢ne : Neutral A → 𝔹 PE.≢ A
𝔹≢ne () PE.refl

Empty≢ne : Neutral A → Empty PE.≢ A
Empty≢ne () PE.refl

Unit≢ne : Neutral A → Unit PE.≢ A
Unit≢ne () PE.refl

B≢ne : ∀ W → Neutral A → ⟦ W ⟧ F ▹ G PE.≢ A
B≢ne BΠ () PE.refl
B≢ne BΣ () PE.refl

U≢B : ∀ W → U PE.≢ ⟦ W ⟧ F ▹ G
U≢B BΠ ()
U≢B BΣ ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B BΠ ()
ℕ≢B BΣ ()

𝔹≢B : ∀ W → 𝔹 PE.≢ ⟦ W ⟧ F ▹ G
𝔹≢B BΠ ()
𝔹≢B BΣ ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B BΠ ()
Empty≢B BΣ ()

Unit≢B : ∀ W → Unit PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B BΠ ()
Unit≢B BΣ ()

zero≢ne : Neutral t → zero PE.≢ t
zero≢ne () PE.refl

suc≢ne : Neutral t → suc u PE.≢ t
suc≢ne () PE.refl

true≢ne : Neutral t → true PE.≢ t
true≢ne () PE.refl

false≢ne : Neutral t → false PE.≢ t
false≢ne () PE.refl

-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural {n : Nat} : Term n → Set where
  zeroₙ :             Natural zero
  sucₙ  :             Natural (suc t)
  ne    : Neutral t → Natural t


-- A whnf of type 𝔹 is either true, false, or neutral.

data Boolean {n : Nat} : Term n → Set where
  trueₙ :             Boolean true
  falseₙ  :           Boolean false
  ne    : Neutral t → Boolean t

-- A (small) type in whnf is either Π A B, Σ A B, ℕ, Empty, Unit or neutral.
-- Large types could also be U.

data Type {n : Nat} : Term n → Set where
  Πₙ     :             Type (Π A ▹ B)
  Σₙ     :             Type (Σ A ▹ B)
  ℕₙ     :             Type ℕ
  𝔹ₙ     :             Type 𝔹
  Emptyₙ :             Type Empty
  Unitₙ  :             Type Unit
  ne     : Neutral t → Type t

⟦_⟧-type : ∀ (W : BindingType) → Type (⟦ W ⟧ F ▹ G)
⟦ BΠ ⟧-type = Πₙ
⟦ BΣ ⟧-type = Σₙ

-- A whnf of type Π A ▹ B is either lam t or neutral.

data Function {n : Nat} : Term n → Set where
  lamₙ : Function (lam t)
  ne   : Neutral t → Function t

-- A whnf of type Σ A ▹ B is either prod t u or neutral.

data Product {n : Nat} : Term n → Set where
  prodₙ : Product (prod t u)
  ne    : Neutral t → Product t

-- These views classify only whnfs.
-- Natural, Type, Function and Product are a subsets of Whnf.

naturalWhnf : ∀ {l : LCon} → Natural t → Whnf {l} t
naturalWhnf sucₙ   = sucₙ
naturalWhnf zeroₙ  = zeroₙ
naturalWhnf (ne x) = ne x

booleanWhnf : ∀ {l : LCon} → Boolean t → Whnf {l} t
booleanWhnf trueₙ   = trueₙ
booleanWhnf falseₙ  = falseₙ
booleanWhnf (ne x) = ne x

typeWhnf : ∀ {l : LCon} → Type A → Whnf {l} A
typeWhnf Πₙ     = Πₙ
typeWhnf Σₙ     = Σₙ
typeWhnf ℕₙ     = ℕₙ
typeWhnf 𝔹ₙ     = 𝔹ₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Unitₙ  = Unitₙ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {l : LCon} → Function t → Whnf {l} t
functionWhnf lamₙ   = lamₙ
functionWhnf (ne x) = ne x

productWhnf : ∀ {l : LCon} → Product t → Whnf {l} t
productWhnf prodₙ  = prodₙ
productWhnf (ne x) = ne x

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
  wkNeutral ρ (Emptyrecₙ e) = Emptyrecₙ (wkNeutral ρ e)
  wkNeutral ρ (αₙ e) = αₙ (wkContainsNeutral ρ e)

  wkContainsNeutral : ∀ ρ → ContainsNeutral t → ContainsNeutral {n} (wk ρ t)
  wkContainsNeutral ρ (ncontn t) = ncontn (wkNeutral ρ t)
  wkContainsNeutral ρ (Scontn t) = Scontn (wkContainsNeutral ρ t)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ ρ → Natural t → Natural {n} (wk ρ t)
wkNatural ρ sucₙ   = sucₙ
wkNatural ρ zeroₙ  = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ ρ → Type t → Type {n} (wk ρ t)
wkType ρ Πₙ     = Πₙ
wkType ρ Σₙ     = Σₙ
wkType ρ ℕₙ     = ℕₙ
wkType ρ 𝔹ₙ     = 𝔹ₙ
wkType ρ Emptyₙ = Emptyₙ
wkType ρ Unitₙ  = Unitₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ ρ → Function t → Function {n} (wk ρ t)
wkFunction ρ lamₙ   = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkProduct : ∀ ρ → Product t → Product {n} (wk ρ t)
wkProduct ρ prodₙ  = prodₙ
wkProduct ρ (ne x) = ne (wkNeutral ρ x)

wkTrueNat : ∀ ρ → TrueNat t → TrueNat {n} (wk ρ t)
wkTrueNat ρ Truezero = Truezero
wkTrueNat ρ (Truesuc tε) = Truesuc (wkTrueNat _ tε)

wkDifferentNat : ∀ {n m } (ρ : Wk m n) (t u : Term n) → DifferentNat t u → DifferentNat {m} (wk ρ t) (wk ρ u)
wkDifferentNat ρ _ _ (Diff0r _ tε) = Diff0r _ (wkTrueNat _ tε)
wkDifferentNat ρ _ _ (Diff0l _ tε) = Diff0l _ (wkTrueNat _ tε)
wkDifferentNat ρ _ _ (DiffSuc _ _ e) = DiffSuc _ _ (wkDifferentNat ρ _ _ e)


wkNatToTerm :  ∀ {n m } (ρ : Wk m n) (t : Nat) →  wk ρ (natToTerm n t) PE.≡ natToTerm m t
wkNatToTerm ρ Nat.zero = PE.refl
wkNatToTerm ρ (1+ t) rewrite (wkNatToTerm ρ t) = PE.refl

wkBboolToTerm :  ∀ {n m } (ρ : Wk m n) (b : Bbool) →  wk ρ (BboolToTerm n b) PE.≡ BboolToTerm m b
wkBboolToTerm ρ Btrue = PE.refl
wkBboolToTerm ρ Bfalse = PE.refl

wkInLCon : ∀ l ρ → InLCon t b l → InLCon {n} (wk ρ t) (wk ρ b) l 
wkInLCon _ ρ (InHere t b l) rewrite  (wkBboolToTerm ρ b) rewrite (wkNatToTerm ρ t) = InHere t b l
wkInLCon _ ρ (InThere t b l tbε t2 b2) = InThere _ _ l (wkInLCon l ρ tbε) t2 b2

wkNotInLCon : ∀ l ρ → NotInLCon t l → NotInLCon {n} (wk ρ t) l 
wkNotInLCon _ ρ (NotInε tε) = NotInε (wkTrueNat _ tε)
wkNotInLCon (addₗ m b γ) ρ (NotInThere .γ γε .m .b e) = NotInThere γ (wkNotInLCon _ _ γε) m b (PE.subst (λ h → DifferentNat _ h) ((wkNatToTerm ρ m)) (wkDifferentNat ρ _ _ e))

wkWhnf : ∀ {l} ρ → Whnf {l} t → Whnf {l} {n} (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Σₙ      = Σₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ 𝔹ₙ      = 𝔹ₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ Unitₙ   = Unitₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ prodₙ   = prodₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ trueₙ   = trueₙ
wkWhnf ρ falseₙ   = falseₙ
wkWhnf ρ starₙ   = starₙ
wkWhnf ρ (ne x)  = ne (wkNeutral ρ x)
wkWhnf ρ (αₙ tε) = αₙ (wkNotInLCon _ _ tε)

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
