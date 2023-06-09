module Example.Outline where

open import Prelude

variable
  n : ℕ
  b b' b₀ b₁ b₂ b₃ : Bool
  d : Mode

-- Simplest types (with metavariables)

-- Syntax.Simple.Term
data TExp (m : ℕ) : Set where
  `_   : Fin m           → TExp m
  base :                   TExp m
  imp  : TExp m → TExp m → TExp m

-- Metavariables used only in typing rules and not elsewhere
Ty : Set
Ty = TExp 0

variable
  σ τ : Ty
  Γ   : List Ty

-- From parser generators to type-inferencer generators
-- Using datatype-generic programming to quantify over simple type systems
-- Only an overall picture in this file (no datatype-generic implementations)

-- The programmer writes untyped terms, whose types should be inferred
-- General type inference quickly becomes undecidable; introduce type annotations
-- Type checking subsumed by type inference

data Raw : ℕ → Set where
  `_  : Fin n         → Raw n
  _∋_ : Ty → Raw n    → Raw n
  app : Raw n → Raw n → Raw n
  abs : Raw (suc n)   → Raw n

variable r r' s s' : Raw _

-- The typing relation for simply typed λ-calculus

infix 3 _⊢_⦂_

data _⊢_⦂_ : (Γ : List Ty) → Raw (length Γ) → Ty → Set where

  `_  : (i : τ ∈ Γ)
      → ---------------------
        Γ ⊢ (` L.index i) ⦂ τ

  _∋_ : (τ : Ty)
      → Γ ⊢ r ⦂ τ
      → ---------------
        Γ ⊢ (τ ∋ r) ⦂ τ

  app : Γ ⊢ r ⦂ imp σ τ
      → Γ ⊢ s ⦂ σ
      → ---------------
        Γ ⊢ app r s ⦂ τ

  abs : σ ∷ Γ ⊢ r ⦂ τ
      → -------------------
        Γ ⊢ abs r ⦂ imp σ τ

-- Decide whether there is a typing derivation for a given raw term
-- if the raw term satisfies some constraint, e.g., having enough type annotations

TypeInference' : (∀ {n} → Raw n → Set) → Set
TypeInference' P = (Γ : List Ty) (r : Raw (length Γ))
                 → P r → Dec (Σ[ τ ∈ Ty ] Γ ⊢ r ⦂ τ)

-- Decide whether a given raw term has a type
-- or abort with the excuse that the term doesn’t satisfy the constraint

TypeInference : (∀ {n} → Raw n → Set) → Set
TypeInference P = (Γ : List Ty) (r : Raw (length Γ))
                → Dec (Σ[ τ ∈ Ty ] Γ ⊢ r ⦂ τ) ⊎ ¬ P r

-- The second version is stronger (and more convenient to use)

TypeInference-lemma : {P : ∀ {n} → Raw n → Set} → TypeInference P → TypeInference' P
TypeInference-lemma infer Γ r p
    with infer Γ r
... | inl  d = d
... | inr ¬p with ¬p p
...          | ()

-- Bidirectional type system for STLC
-- Terms are syntactically classified into two categories
-- based on whether their types can be inferred or (only) checked

data HasMode : Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → -----------------
        HasMode Inf (` i)

  _∋_ : (τ : Ty)
      → HasMode Chk r
      → -------------------
        HasMode Inf (τ ∋ r)

  _↑  : HasMode Inf r
      → -------------
        HasMode Chk r

  app : HasMode Inf r
      → HasMode Chk s
      → ---------------------
        HasMode Inf (app r s)

  abs : HasMode Chk r
      → -------------------
        HasMode Chk (abs r)

-- First step: syntactically decide whether there are enough type annotations
-- Wherever a checked term needs to be used as an inferred term,
-- a type annotation is necessary, e.g., app (abs t ∋ imp σ τ) u

Bidirectionalisation : Set
Bidirectionalisation = ∀ {n} (r : Raw n) → Dec (HasMode Inf r)

-- Second step: bidirectional type inference
-- If a bidirectional type system is designed well (i.e., mode-correct),
-- from inferred types we can derive what the types of checked terms should be

infix 3 _⊢_[_]_ _⊢_⇐_ _⊢_⇒_

mutual

  _⊢_⇐_ _⊢_⇒_ : (Γ : List Ty) → Raw (length Γ) → Ty → Set
  Γ ⊢ r ⇐ τ = Γ ⊢ r [ Chk ] τ
  Γ ⊢ r ⇒ τ = Γ ⊢ r [ Inf ] τ

  data _⊢_[_]_ : (Γ : List Ty) → Raw (length Γ) → Mode → Ty → Set where

    `_  : (i : τ ∈ Γ)
        → ---------------------
          Γ ⊢ (` L.index i) ⇒ τ

    _∋_ : (τ : Ty)
        → Γ ⊢ r ⇐ τ
        → ---------------
          Γ ⊢ (τ ∋ r) ⇒ τ

    _↑_ : Γ ⊢ r ⇒ σ
        → σ ≡ τ
        → ---------
          Γ ⊢ r ⇐ τ

    app : Γ ⊢ r ⇒ imp σ τ
        → Γ ⊢ s ⇐ σ
        → ---------------
          Γ ⊢ app r s ⇒ τ

    abs : σ ∷ Γ ⊢ r ⇐ τ
        → -------------------
          Γ ⊢ abs r ⇐ imp σ τ

TypeInference⇔ : Set
TypeInference⇔ = (Γ : List Ty) {r : Raw (length Γ)}
               → HasMode Inf r → Dec (Σ[ τ ∈ Ty ] Γ ⊢ r ⇒ τ)

-- Eventually we want to perform ordinary type inference (the spec)
-- using bidirectional type inference (the impl);
-- the two type systems should be somehow related to make that possible

Soundness : Set
Soundness = {Γ : List Ty} {r : Raw (length Γ)} {d : Mode} {τ : Ty}
          → Γ ⊢ r [ d ] τ  →  Γ ⊢ r ⦂ τ

soundness : Soundness
soundness (` i)      = ` i
soundness (τ ∋ t)    = τ ∋ soundness t
soundness (t ↑ refl) = soundness t
soundness (app t u)  = app (soundness t) (soundness u)
soundness (abs t)    = abs (soundness t)

Completeness : Set
Completeness = {Γ : List Ty} {r : Raw (length Γ)} {d : Mode} {τ : Ty}
             → HasMode d r  →  Γ ⊢ r ⦂ τ  →  Γ ⊢ r [ d ] τ

completeness : Completeness
completeness (` ._)    (` i)     = ` i
completeness (._ ∋ p)  (τ ∋ t)   = τ ∋ completeness p t
completeness (p ↑)     t         = completeness p t ↑ refl
completeness (app p q) (app t u) = app (completeness p t) (completeness q u)
completeness (abs p)   (abs t)   = abs (completeness p t)

infer : Bidirectionalisation → TypeInference⇔
      → Soundness → Completeness
      → TypeInference (HasMode Inf)
infer bidir infer⇔ s c Γ r with bidir r
... | yes p = inl (map′ (map₂ s) (map₂ (c p)) (infer⇔ Γ p))
... | no ¬p = inr ¬p

--   Γ ⊢ r ⦂ τ   ←   Γ ⊢ r ⇒ τ
--
--     ↑               ↑
--
--   r : Raw n   →   HasMode Inf r

data And : List Bool → Bool → Set where
  nil :                     And []           true
  hd  : ∀ {bs}            → And (false ∷ bs) false
  tl  : ∀ {bs} → And bs b → And (true  ∷ bs) b

data HasMode' : Bool → Bool → Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ----------------------------
        HasMode' true true Inf (` i)

  _↑  : HasMode' true b Inf r
      → ----------------------
        HasMode' false b Chk r

  _∋_ : (τ : Ty)
      → HasMode' b' b Chk r
      → ---------------------------
        HasMode' true b Inf (τ ∋ r)

  ?∋_ : HasMode' true b Chk r
      → --------------------------
        HasMode' false false Inf r

  app : HasMode' b₀ b₁ Inf r
      → HasMode' b₂ b₃ Chk s
      → And (b₁ ∷ b₃ ∷ []) b
      → -----------------------------
        HasMode' true b Inf (app r s)

  abs : HasMode' b' b Chk r
      → ---------------------------
        HasMode' true b Chk (abs r)

hasMode : HasMode' b true d r → HasMode d r
hasMode (` i)   = ` i
hasMode (t ↑)   = hasMode t ↑
hasMode (τ ∋ t) = τ ∋ hasMode t
hasMode (app t u (tl (tl nil))) = app (hasMode t) (hasMode u)
hasMode (abs t) = abs (hasMode t)

¬hasMode-Inf : HasMode' true b Chk r → ¬ HasMode Inf r
¬hasMode-Inf (abs t) ()

mutual

  ¬hasMode-Chk : HasMode' true false Inf r → ¬ HasMode Chk r
  ¬hasMode-Chk (τ ∋ t)            ((.τ ∋ u) ↑) = ¬hasMode t u
  ¬hasMode-Chk (app t t' hd)      (app u u' ↑) = ¬hasMode t u
  ¬hasMode-Chk (app t t' (tl hd)) (app u u' ↑) = ¬hasMode t' u'

  ¬hasMode : HasMode' b false d r → ¬ HasMode d r
  ¬hasMode (t ↑)              u          = ¬hasMode-Chk t u
  ¬hasMode (τ ∋ t)            (.τ ∋ u)   = ¬hasMode t u
  ¬hasMode (?∋ t)             u          = ¬hasMode-Inf t u
  ¬hasMode (app t t' hd)      (app u u') = ¬hasMode t u
  ¬hasMode (app t t' (tl hd)) (app u u') = ¬hasMode t' u'
  ¬hasMode (abs t)            (abs u)    = ¬hasMode t u

data _≤ᴬ_ : {n : ℕ} → Raw n → Raw n → Set where

  `_   : (i : Fin n)
       → --------------
         (` i) ≤ᴬ (` i)

  _∋_  : (τ : Ty)
       → r ≤ᴬ r'
       → -------------------
         (τ ∋ r) ≤ᴬ (τ ∋ r')

  _∋'_ : (τ : Ty)
       → r ≤ᴬ r'
       → -------------
         r ≤ᴬ (τ ∋ r')

  app  : r ≤ᴬ r'
       → s ≤ᴬ s'
       → --------------------
         app r s ≤ᴬ app r' s'

  abs  : r ≤ᴬ r'
       → ---------------
         abs r ≤ᴬ abs r'
