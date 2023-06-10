{-# OPTIONS --safe #-}

module Example.Outline where

open import Prelude

variable
  n : ℕ
  v v₀ v₁ e e₀ e₁ : Bool
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
TypeInference E = (Γ : List Ty) (r : Raw (length Γ))
                → Dec (Σ[ τ ∈ Ty ] Γ ⊢ r ⦂ τ) ⊎ E r

-- The second version is logically stronger and more useful in practice

TypeInference-lemma : {P : ∀ {n} → Raw n → Set} → TypeInference (¬_ ∘ P) → TypeInference' P
TypeInference-lemma infer Γ r p
    with infer Γ r
... | inl  d = d
... | inr ¬p with ¬p p
...          | ()

-- Bidirectional type system for STLC
-- Terms are syntactically classified into two categories
-- based on whether their types can be inferred or (only) checked

data Pre : Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → -----------------
        Pre Inf (` i)

  _∋_ : (τ : Ty)
      → Pre Chk r
      → -------------------
        Pre Inf (τ ∋ r)

  _↑  : Pre Inf r
      → -------------
        Pre Chk r

  app : Pre Inf r
      → Pre Chk s
      → ---------------------
        Pre Inf (app r s)

  abs : Pre Chk r
      → -------------------
        Pre Chk (abs r)

-- First step: syntactically decide whether there are enough type annotations
-- Wherever a checked term needs to be used as an inferred term,
-- a type annotation is necessary, e.g., app (abs t ∋ imp σ τ) u

Bidirectionalisation : Set
Bidirectionalisation = ∀ {n} (r : Raw n) → Dec (Pre Inf r)

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
               → Pre Inf r → Dec (Σ[ τ ∈ Ty ] Γ ⊢ r ⇒ τ)

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
             → Pre d r  →  Γ ⊢ r ⦂ τ  →  Γ ⊢ r [ d ] τ

completeness : Completeness
completeness (` ._)    (` i)     = ` i
completeness (._ ∋ p)  (τ ∋ t)   = τ ∋ completeness p t
completeness (p ↑)     t         = completeness p t ↑ refl
completeness (app p q) (app t u) = app (completeness p t) (completeness q u)
completeness (abs p)   (abs t)   = abs (completeness p t)

infer : Bidirectionalisation → TypeInference⇔
      → Soundness → Completeness
      → TypeInference (¬_ ∘ Pre Inf)
infer bidir infer⇔ s c Γ r with bidir r
... | yes p = inl (map′ (map₂ s) (map₂ (c p)) (infer⇔ Γ p))
... | no ¬p = inr ¬p

--   Γ ⊢ r ⦂ τ   ←   Γ ⊢ r ⇒ τ
--
--     ↑               ↑
--
--   r : Raw n   →   Pre Inf r

-- Strengthening bidirectionalisation

data Pre? : (valid exact : Bool) → Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ------------------------
        Pre? true true Inf (` i)

  _∋_ : (τ : Ty)
      → Pre? v e    Chk      r
      → -----------------------
        Pre? v true Inf (τ ∋ r)

  _↑  : Pre? v true  Inf r
      → ------------------
        Pre? v false Chk r

  ?∋_ : Pre? v     true  Chk r
      → ----------------------
        Pre? false false Inf r

  app : Pre? v₀ e₀ Inf r
      → Pre? v₁ e₁ Chk s
      → And (v₀ ∷ v₁ ∷ []) v
      → -------------------------
        Pre? v true Inf (app r s)

  abs : Pre? v e    Chk      r
      → -----------------------
        Pre? v true Chk (abs r)

app-abs : Pre? false true Inf {zero} (app (abs (` zero)) (abs (` zero)))
app-abs = app (?∋ abs ((` zero) ↑)) (abs ((` zero) ↑)) hd

toPre : Pre? true e d r → Pre d r
toPre (` i)   = ` i
toPre (τ ∋ t) = τ ∋ toPre t
toPre (t ↑)   = toPre t ↑
toPre (app t u (tl (tl nil))) = app (toPre t) (toPre u)
toPre (abs t) = abs (toPre t)

to¬Pre-Inf : Pre? v true Chk r → ¬ Pre Inf r
to¬Pre-Inf (abs t) ()

mutual

  to¬Pre-Chk : Pre? false true Inf r → ¬ Pre Chk r
  to¬Pre-Chk (τ ∋ t)            ((.τ ∋ u) ↑) = to¬Pre t u
  to¬Pre-Chk (app t t' hd)      (app u u' ↑) = to¬Pre t u
  to¬Pre-Chk (app t t' (tl hd)) (app u u' ↑) = to¬Pre t' u'

  to¬Pre : Pre? false e d r → ¬ Pre d r
  to¬Pre (τ ∋ t)            (.τ ∋ u)   = to¬Pre t u
  to¬Pre (t ↑)              u          = to¬Pre-Chk t u
  to¬Pre (?∋ t)             u          = to¬Pre-Inf t u
  to¬Pre (app t t' hd)      (app u u') = to¬Pre t u
  to¬Pre (app t t' (tl hd)) (app u u') = to¬Pre t' u'
  to¬Pre (abs t)            (abs u)    = to¬Pre t u

Bidirectionalisation⁺ : Set
Bidirectionalisation⁺ = ∀ {n} (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e Inf r

Bidirectionalisation-lemma : Bidirectionalisation⁺ → Bidirectionalisation
Bidirectionalisation-lemma bidir⁺ r with bidir⁺ r
... | false , _ , p = no (to¬Pre p)
... | true  , _ , p = yes (toPre p)

mutual

  bidirectionalise : (d : Mode) (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e d r
  bidirectionalise d   r with bidirectionalise' r
  bidirectionalise Chk r | inl               t     = _ , _ ,    t ↑
  bidirectionalise Inf r | inl               t     = _ , _ ,    t
  bidirectionalise Chk r | inr (inl          t   ) = _ , _ ,    t
  bidirectionalise Inf r | inr (inl          t   ) = _ , _ , ?∋ t
  bidirectionalise Chk r | inr (inr (_     , t  )) = _ , _ ,    t
  bidirectionalise Inf r | inr (inr (false , t ↑)) = _ , _ ,    t
  bidirectionalise Inf r | inr (inr (true  , t  )) = _ , _ , ?∋ t

  bidirectionalise'
    : (r : Raw n)
    →        Pre? true  true Inf r
    ⊎        Pre? true  true Chk r
    ⊎ ∃[ e ] Pre? false e    Chk r
  bidirectionalise' (` i) = inl (` i)
  bidirectionalise' (τ ∋ r) with bidirectionalise Chk r
  ... | false , _ , p = inr (inr (_ , (τ ∋ p) ↑))
  ... | true  , _ , p = inl (          τ ∋ p    )
  bidirectionalise' (app r s) with bidirectionalise Inf r | bidirectionalise Chk s
  ... | false , _ , p | v     , _ , q = inr (inr (_ , app p q  hd        ↑))
  ... | true  , _ , p | false , _ , q = inr (inr (_ , app p q (tl  hd)   ↑))
  ... | true  , _ , p | true  , _ , q = inl (         app p q (tl (tl nil)))
  bidirectionalise' (abs r) with bidirectionalise Chk r
  ... | false , _ , p = inr (inr (_ , abs p))
  ... | true  , _ , p = inr (inl (    abs p))

infix 3 _≤ᴬ_

data _≤ᴬ_ : {n : ℕ} → Raw n → Raw n → Set where

  `_   : (i : Fin n)
       → --------------
         (` i) ≤ᴬ (` i)

  _∋_  : (τ : Ty)
       → r ≤ᴬ r'
       → -------------------
         (τ ∋ r) ≤ᴬ (τ ∋ r')

  _∋⁺_ : (τ : Ty)
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

annotatability
  : {r : Raw (length Γ)} → Pre? v e d r
  → Γ ⊢ r ⦂ τ → Σ[ r' ∈ Raw (length Γ) ] r ≤ᴬ r' × Γ ⊢ r' [ d ] τ
annotatability (` .(L.index i)) (` i) = _ , ` (L.index i) , ` i
annotatability (p ↑) t with annotatability p t
... | _ , r≤r' , t' = _ , r≤r' , t' ↑ refl
annotatability (τ ∋ p) (.τ ∋ t) with annotatability p t
... | _ , r≤r' , t' = _ , τ ∋ r≤r' , τ ∋ t'
annotatability (?∋ p) t with annotatability p t
... | _ , r≤r' , t' = _ , _ ∋⁺ r≤r' , _ ∋ t'
annotatability (app p q _) (app t u) with annotatability p t | annotatability q u
... | _ , r≤r' , t' | _ , s≤s' , u' = _ , app r≤r' s≤s' , app t' u'
annotatability (abs p) (abs t) with annotatability p t
... | _ , r≤r' , t' = _ , abs r≤r' , abs t'
