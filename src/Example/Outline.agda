{-# OPTIONS --safe #-}

module Example.Outline where

open import Prelude

variable
  n    : ℕ
  mode : Mode

-- From parser generators to type-inferencer generators
-- Using datatype-generic programming to quantify over simple type systems
-- Only an overall picture in this file (no datatype-generic implementations)

-- Simplest types (with metavariables)

-- Syntax.Simple.Term
data TExp (m : ℕ) : Set where
  `_   : Fin m → TExp m
  base : TExp m
  imp  : TExp m → TExp m → TExp m

-- Metavariables used only in typing rules and not elsewhere
Ty : Set
Ty = TExp 0

variable
  σ τ : Ty
  Γ   : List Ty

-- Simply typed λ-calculus, intrinsically scoped and typed

data Core : Ty → List Ty → Set where
  `_  : τ ∈ Γ → Core τ Γ
  app : Core (imp σ τ) Γ → Core σ Γ → Core τ Γ
  abs : Core τ (σ ∷ Γ) → Core (imp σ τ) Γ

-- The programmer writes untyped terms, whose types should be inferred
-- General type inference quickly becomes undecidable; introduce type annotations
-- Type checking subsumed by type inference

data Raw : ℕ → Set where
  `_  : Fin n → Raw n
  _∋_ : Ty → Raw n → Raw n
  app : Raw n → Raw n → Raw n
  abs : Raw (suc n) → Raw n

variable r s : Raw _

-- Including type annotations in typed terms to ensure that they are respected

data Typed : Ty → List Ty → Set where
  `_  : τ ∈ Γ → Typed τ Γ
  _∋_ : (τ : Ty) → Typed τ Γ → Typed τ Γ
  app : Typed (imp σ τ) Γ → Typed σ Γ → Typed τ Γ
  abs : Typed τ (σ ∷ Γ) → Typed (imp σ τ) Γ

-- Goal: ‘invert’ the following function

eraseType : Typed τ Γ → Raw (length Γ)
eraseType (` i)     = ` L.index i
eraseType (τ ∋ t)   = τ ∋  eraseType t
eraseType (app t u) = app (eraseType t) (eraseType u)
eraseType (abs t)   = abs (eraseType t)

-- Remove type annotations for subsequent development

toCore : Typed τ Γ → Core τ Γ
toCore (` i)     = ` i
toCore (τ ∋ t)   = toCore t
toCore (app t u) = app (toCore t) (toCore u)
toCore (abs t)   = abs (toCore t)

-- Intrinsically enforcing the inversion equation (algebraic ornamentation)
-- Typing τ Γ r  ≅  Σ[ t ∈ Typed τ Γ ] eraseType t ≡ r

data Typing : Ty → (Γ : List Ty) → Raw (length Γ) → Set where
  `_  : (i : τ ∈ Γ) → Typing τ Γ (` L.index i)
  _∋_ : (τ : Ty) → Typing τ Γ r → Typing τ Γ (τ ∋ r)
  app : Typing (imp σ τ) Γ r → Typing σ Γ s → Typing τ Γ (app r s)
  abs : Typing τ (σ ∷ Γ) r → Typing (imp σ τ) Γ (abs r)

-- Decide whether there is a typed term that erases to the given raw term
-- (or a typing derivation for the given raw term)
-- if the raw term satisfies some constraint, e.g., having enough type annotations

TypeInference' : (∀ {n} → Raw n → Set) → Set
TypeInference' P = (Γ : List Ty) (r : Raw (length Γ))
                 → P r → Dec (Σ[ τ ∈ Ty ] Typing τ Γ r)

-- Decide whether a given raw term has a type
-- or abort with the excuse that the term doesn’t satisfy the constraint

TypeInference : (∀ {n} → Raw n → Set) → Set
TypeInference P = (Γ : List Ty) (r : Raw (length Γ))
                → Dec (Σ[ τ ∈ Ty ] Typing τ Γ r) ⊎ ¬ P r

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
-- If a bidirectional type system is designed well (i.e., mode-correct),
-- from inferred types we can derive what the types of checked terms should be

-- ~ Syntax.BiTyped.Intrinsic.Term
data Typed⇆ : Ty → List Ty → Mode → Set where
  `_   : (i : τ ∈ Γ) → Typed⇆ τ Γ Syn  -- context is known
  _∋_  : (τ : Ty) → Typed⇆ τ Γ Chk → Typed⇆ τ Γ Syn
  _↑_  : Typed⇆ σ Γ Syn → σ ≡ τ → Typed⇆ τ Γ Chk
  app  : Typed⇆ (imp σ τ) Γ Syn → Typed⇆ σ Γ Chk → Typed⇆ τ Γ Syn
  abs  : Typed⇆ τ (σ ∷ Γ) Chk → Typed⇆ (imp σ τ) Γ Chk

-- Bidirectional raw terms, retaining only the modes

-- It is possible to syntactically decide whether there are enough type annotations:
-- wherever a checked term needs to be used as an inferred term,
-- a type annotation is necessary, e.g., app (abs t ∋ imp σ τ) u

data Raw⇆ : ℕ → Mode → Set where
  `_   : Fin n → Raw⇆ n Syn
  _∋_  : Ty → Raw⇆ n Chk → Raw⇆ n Syn
  _↑   : Raw⇆ n Syn → Raw⇆ n Chk
  app  : Raw⇆ n Syn → Raw⇆ n Chk → Raw⇆ n Syn
  abs  : Raw⇆ (suc n) Chk → Raw⇆ n Chk

variable r' s' : Raw⇆ _ _

-- First step: see if we can successfully assign modes to raw terms
-- Same inversion story

eraseMode : Raw⇆ n mode → Raw n
eraseMode (` i)       = ` i
eraseMode (τ ∋ r')    = τ ∋ eraseMode r'
eraseMode (r' ↑)      = eraseMode r'
eraseMode (app r' s') = app (eraseMode r') (eraseMode s')
eraseMode (abs r')    = abs (eraseMode r')

data HasMode : {n : ℕ} → Mode → Raw n → Set where
  `_  : (i : Fin n) → HasMode Syn (` i)
  _∋_ : (τ : Ty) → HasMode Chk r → HasMode Syn (τ ∋ r)
  _↑  : HasMode Syn r → HasMode Chk r
  app : HasMode Syn r → HasMode Chk s → HasMode Syn (app r s)
  abs : HasMode Chk r → HasMode Chk (abs r)

Bidirectionalisation : Set
Bidirectionalisation = {n : ℕ} (r : Raw n) → Dec (HasMode Syn r)

toRaw⇆ : {r : Raw n} → HasMode mode r → Raw⇆ n mode
toRaw⇆ (` i)     = ` i
toRaw⇆ (τ ∋ p)   = τ ∋ toRaw⇆ p
toRaw⇆ (p ↑)     = toRaw⇆ p ↑
toRaw⇆ (app p q) = app (toRaw⇆ p) (toRaw⇆ q)
toRaw⇆ (abs p)   = abs (toRaw⇆ p)

-- Second step: bidirectional type inference
-- Same inversion story again!

eraseType⇆ : Typed⇆ τ Γ mode → Raw⇆ (length Γ) mode
eraseType⇆ (` i)     = ` L.index i
eraseType⇆ (τ ∋ t)   = τ ∋ eraseType⇆ t
eraseType⇆ (t ↑ eq)  = (eraseType⇆ t) ↑
eraseType⇆ (app t u) = app (eraseType⇆ t) (eraseType⇆ u)
eraseType⇆ (abs t)   = abs (eraseType⇆ t)

data Typing⇆ : Ty → (Γ : List Ty) {mode : Mode} → Raw⇆ (length Γ) mode → Set where
  `_  : (i : τ ∈ Γ) → Typing⇆ τ Γ (` L.index i)
  _∋_ : (τ : Ty) → Typing⇆ τ Γ r' → Typing⇆ τ Γ (τ ∋ r')
  _↑_ : Typing⇆ σ Γ r' → σ ≡ τ → Typing⇆ τ Γ (r' ↑)
  app : Typing⇆ (imp σ τ) Γ r' → Typing⇆ σ Γ s' → Typing⇆ τ Γ (app r' s')
  abs : Typing⇆ τ (σ ∷ Γ) r' → Typing⇆ (imp σ τ) Γ (abs r')

TypeInference⇆ : Set
TypeInference⇆ = (Γ : List Ty) (r' : Raw⇆ (length Γ) Syn)
               → Dec (Σ[ τ ∈ Ty ] Typing⇆ τ Γ r')

-- Eventually we want to perform ordinary type inference (the spec)
-- using bidirectional type inference (the impl);
-- the two type systems should be somehow related to make that possible

Soundness : Set
Soundness = {τ : Ty} {Γ : List Ty} {r : Raw (length Γ)} {mode : Mode}
            (p : HasMode mode r) → Typing⇆ τ Γ (toRaw⇆ p) → Typing τ Γ r

soundness : Soundness
soundness (` ._)    (` i)      = ` i
soundness (._ ∋ p)  (τ ∋ t)    = τ ∋ soundness p t
soundness (p ↑)     (t ↑ refl) = soundness p t
soundness (app p q) (app t u)  = app (soundness p t) (soundness q u)
soundness (abs p)   (abs t)    = abs (soundness p t)

Completeness : Set
Completeness = {τ : Ty} {Γ : List Ty} {r : Raw (length Γ)} {mode : Mode}
               (p : HasMode mode r) → Typing τ Γ r → Typing⇆ τ Γ (toRaw⇆ p)

completeness : Completeness
completeness (` ._)    (` i)     = ` i
completeness (._ ∋ p)  (τ ∋ t)   = τ ∋ completeness p t
completeness (p ↑)     t         = completeness p t ↑ refl
completeness (app p q) (app t u) = app (completeness p t) (completeness q u)
completeness (abs p)   (abs t)   = abs (completeness p t)

infer : Bidirectionalisation → TypeInference⇆
      → Soundness → Completeness
      → TypeInference (HasMode Syn)
infer bidir infer⇆ s c Γ r with bidir r
... | yes p = inl (map′ (map₂ (s p)) (map₂ (c p)) (infer⇆ Γ (toRaw⇆ p)))
... | no ¬p = inr ¬p

{-

Core τ Γ   ←   Typed τ Γ

                 ↑

               Typing τ Γ r            ←           Typing⇆ τ Γ Syn r'

                 ↑                                    ↑

               r : Raw n   →   HasMode Syn r   →   r' : Raw⇆ n Syn

-}
