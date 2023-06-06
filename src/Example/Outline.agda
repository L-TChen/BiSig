module Example.Outline where

open import Prelude

variable n : ℕ

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

variable r s : Raw _

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

data HasMode : {n : ℕ} → Mode → Raw n → Set where

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
-- If a bidirectional type system is designed well (i.e., d-correct),
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
          → HasMode d r  →  Γ ⊢ r [ d ] τ  →  Γ ⊢ r ⦂ τ

soundness : Soundness
soundness (` ._)    (` i)      = ` i
soundness (._ ∋ p)  (τ ∋ t)    = τ ∋ soundness p t
soundness (p ↑)     (t ↑ refl) = soundness p t
soundness (app p q) (app t u)  = app (soundness p t) (soundness q u)
soundness (abs p)   (abs t)    = abs (soundness p t)

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
... | yes p = inl (map′ (map₂ (s p)) (map₂ (c p)) (infer⇔ Γ p))
... | no ¬p = inr ¬p

--   Γ ⊢ r ⦂ τ   ←   Γ ⊢ r ⇒ τ
--
--     ↑               ↑
--
--   r : Raw n   →   HasMode Inf r
