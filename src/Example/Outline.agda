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
  A B : Ty
  Γ   : List Ty

-- From parser generators to type-synthesiser generators
-- Using datatype-generic programming to quantify over simple type systems
-- Only an overall picture in this file (no datatype-generic implementations)

-- The programmer writes untyped terms, whose types should be synthesised
-- General type synthesis quickly becomes undecidable; introduce type annotations
-- Type checking subsumed by type synthesis

data Raw : ℕ → Set where
  `_  : Fin n         → Raw n
  _∋_ : Ty → Raw n    → Raw n
  app : Raw n → Raw n → Raw n
  abs : Raw (suc n)   → Raw n

variable r r' s s' : Raw _

-- The typing relation for simply typed λ-calculus

infix 3 _⊢_⦂_

data _⊢_⦂_ : (Γ : List Ty) → Raw (length Γ) → Ty → Set where

  `_  : (i : A ∈ Γ)
      → ---------------------
        Γ ⊢ (` L.index i) ⦂ A

  _∋_ : (A : Ty)
      → Γ ⊢ r ⦂ A
      → ---------------
        Γ ⊢ (A ∋ r) ⦂ A

  app : Γ ⊢ r ⦂ imp A B
      → Γ ⊢ s ⦂ A
      → ---------------
        Γ ⊢ app r s ⦂ B

  abs : A ∷ Γ ⊢ r ⦂ B
      → -------------------
        Γ ⊢ abs r ⦂ imp A B

-- Decide whether there is a typing derivation for a given raw term
-- if the raw term satisfies some constraint, e.g., having enough type annotations

TypeSynthesis' : (∀ {n} → Raw n → Set) → Set
TypeSynthesis' P = (Γ : List Ty) (r : Raw (length Γ))
                 → P r → Dec (Σ[ A ∈ Ty ] Γ ⊢ r ⦂ A)

-- Decide whether a given raw term has a type
-- or abort with the excuse that the term doesn’t satisfy the constraint

TypeSynthesis : (∀ {n} → Raw n → Set) → Set
TypeSynthesis E = (Γ : List Ty) (r : Raw (length Γ))
                → Dec (Σ[ A ∈ Ty ] Γ ⊢ r ⦂ A) ⊎ E r

-- The second version is logically stronger and more useful in practice

TypeSynthesis-lemma : {P : ∀ {n} → Raw n → Set} → TypeSynthesis (¬_ ∘ P) → TypeSynthesis' P
TypeSynthesis-lemma syn Γ r p
    with syn Γ r
... | inl  d = d
... | inr ¬p with ¬p p
...          | ()

-- Bidirectional type system for STLC
-- Terms are syntactically classified into two categories
-- based on whether their types can be synthesised or checked

data Pre : Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → -------------
        Pre Syn (` i)

  _∋_ : (A : Ty)
      → Pre Chk r
      → ---------------
        Pre Syn (A ∋ r)

  _↑  : Pre Syn r
      → ---------
        Pre Chk r

  app : Pre Syn r
      → Pre Chk s
      → -----------------
        Pre Syn (app r s)

  abs : Pre Chk r
      → ---------------
        Pre Chk (abs r)

-- First step: syntactically decide whether there are enough type annotations
-- Wherever a checked term needs to be used as an synthesised term,
-- a type annotation is necessary, e.g., app (abs t ∋ imp B A) u

ModePreprocessing : Set
ModePreprocessing = (d : Mode) {n : ℕ} (r : Raw n) → Dec (Pre d r)

-- Second step: bidirectional type synthesis
-- If a bidirectional type system is designed well (i.e., mode-correct),
-- from synthesised types we can derive what the types of checked terms should be

infix 3 _⊢_[_]_ _⊢_⇐_ _⊢_⇒_

mutual

  _⊢_⇐_ _⊢_⇒_ : (Γ : List Ty) → Raw (length Γ) → Ty → Set
  Γ ⊢ r ⇐ A = Γ ⊢ r [ Chk ] A
  Γ ⊢ r ⇒ A = Γ ⊢ r [ Syn ] A

  data _⊢_[_]_ : (Γ : List Ty) → Raw (length Γ) → Mode → Ty → Set where

    var : (j : A ∈ Γ)
        → {i : Fin (length Γ)}
        →  i ≡ L.index j
        → --------------------
          Γ ⊢ ` i ⇒ A

    _∋_ : (A : Ty)
        → Γ ⊢ r ⇐ A
        → ---------------
          Γ ⊢ (A ∋ r) ⇒ A

    _↑_ : Γ ⊢ r ⇒ B
        → A ≡ B
        → ---------
          Γ ⊢ r ⇐ A

    app : Γ ⊢ r ⇒ imp A B
        → Γ ⊢ s ⇐ A
        → ---------------
          Γ ⊢ app r s ⇒ B

    abs : A ∷ Γ ⊢ r ⇐ B
        → -------------------
          Γ ⊢ abs r ⇐ imp A B

TypeSynthesis⇔ : Set
TypeSynthesis⇔ = (Γ : List Ty) {r : Raw (length Γ)}
               → Pre Syn r → Dec (Σ[ A ∈ Ty ] Γ ⊢ r ⇒ A)

module TypeSynthesis⇔ where

  base≢imp : base ≢ imp A B
  base≢imp ()

  imp≡⁻ : {A A′ B B′ : Ty} → imp A B ≡ imp A′ B′ → A ≡ A′ × B ≡ B′
  imp≡⁻ refl = refl , refl

  _≟Ty_ : (A B : Ty) → Dec (A ≡ B)
  base    ≟Ty base    = yes refl
  base    ≟Ty imp A B = no λ ()
  imp A B ≟Ty base    = no λ ()
  imp A B ≟Ty imp C D with A ≟Ty C | B ≟Ty D
  ... | yes A=C | yes B=D = yes (cong₂ imp A=C B=D)
  ... | no  A≠C | _       = no λ where refl → A≠C refl
  ... | _       | no B≠D  = no λ where refl → B≠D refl

  uniq-⇒-var : (i : A ∈ Γ) (j : B ∈ Γ) → L.index i ≡ L.index j → A ≡ B
  uniq-⇒-var (here refl) (here refl) _  = refl
  uniq-⇒-var (there i)   (there j)   eq = uniq-⇒-var i j (F.suc-injective eq)

  uniq-⇒ : {Γ : List Ty} {r : Raw (length Γ)} {A B : Ty} → Pre Syn r
    → Γ ⊢ r ⇒ A → Γ ⊢ r ⇒ B → A ≡ B
  uniq-⇒ _         (var i ieq) (var j jeq) = uniq-⇒-var i j (trans (sym ieq) jeq)
  uniq-⇒ _         (_ ∋ t)     (_ ∋ u)     = refl
  uniq-⇒ (app r _) (app t u)   (app t′ u′) with uniq-⇒ r t t′
  ... | refl = refl

  ¬arg : {Γ : List Ty} {A B : Ty} {t u : Raw (length Γ)}
    → Pre Syn t → Pre Chk u
    → Γ ⊢ t ⇒ imp A B
    → ¬ (Γ ⊢ u ⇐ A)
    --------------------------
    → ¬ (∃[ B′ ] Γ ⊢ app t u ⇒ B′)
  ¬arg t _ ⊢t ¬⊢u (B′ , app ⊢t′ ⊢u′) rewrite imp≡⁻ (uniq-⇒ t ⊢t ⊢t′) .proj₁ = ¬⊢u ⊢u′

  TypeChecking⇔ : Set
  TypeChecking⇔ = (Γ : List Ty) (A : Ty) {r : Raw (length Γ)}
                → Pre Chk r → Dec (Γ ⊢ r ⇐ A)

  mutual
    synthesise : TypeSynthesis⇔
    synthesise Γ (` i) = yes (L.lookup Γ i , var (L.∈-lookup i) (sym (L.index-∈-lookup Γ i)))
    synthesise Γ (A ∋ t) with check Γ A t
    ... | no ¬⊢t = no λ where (B , B ∋ ⊢t) → ¬⊢t ⊢t
    ... | yes ⊢t = yes (A , (A ∋ ⊢t))
    synthesise Γ (app t u) with synthesise Γ t
    ... | no ¬∃              = no λ where (_ , app ⊢t ⊢u) → ¬∃ (_ , ⊢t)
    ... | yes (base    , ⊢t) = no λ where (A , app ⊢t′ ⊢u) → base≢imp (uniq-⇒ t ⊢t ⊢t′)
    ... | yes (imp A B , ⊢t) with check Γ A u
    ... | no ¬⊢u = no (¬arg t u ⊢t ¬⊢u)
    ... | yes ⊢u = yes (B , app ⊢t ⊢u)

    check : TypeChecking⇔
    check Γ A (t ↑) with synthesise Γ t
    ... | no ¬∃ = no λ where
      (⊢t ↑ _) → ¬∃ (_ , ⊢t)
    ... | yes (B , ⊢t) with A ≟Ty B
    ... | no  A≠B = no λ where (⊢u ↑ refl) → A≠B (uniq-⇒ t ⊢u ⊢t)
    ... | yes A=B = yes (⊢t ↑ A=B)
    check Γ base      (abs t) = no λ where (() ↑ _)
    check Γ (imp A B) (abs t) with check (A ∷ Γ) B t
    ... | no ¬⊢t = no λ where
      (abs ⊢t) → ¬⊢t ⊢t
    ... | yes ⊢t = yes (abs ⊢t)

-- Eventually we want to perform ordinary type synthesis (the spec)
-- using bidirectional type synthesis (the impl);
-- the two type systems should be somehow related to make that possible

Soundness : Set
Soundness = {Γ : List Ty} {r : Raw (length Γ)} {d : Mode} {A : Ty}
          → Γ ⊢ r [ d ] A  →  Γ ⊢ r ⦂ A

soundness : Soundness
soundness (var i refl)  = ` i
soundness (A ∋ t)    = A ∋ soundness t
soundness (t ↑ refl) = soundness t
soundness (app t u)  = app (soundness t) (soundness u)
soundness (abs t)    = abs (soundness t)

Completeness : Set
Completeness = {Γ : List Ty} {r : Raw (length Γ)} {d : Mode} {A : Ty}
             → Pre d r  →  Γ ⊢ r ⦂ A  →  Γ ⊢ r [ d ] A

completeness : Completeness
completeness (` ._)    (` i)     = var i refl
completeness (._ ∋ p)  (A ∋ t)   = A ∋ completeness p t
completeness (p ↑)     t         = completeness p t ↑ refl
completeness (app p q) (app t u) = app (completeness p t) (completeness q u)
completeness (abs p)   (abs t)   = abs (completeness p t)

-- Completing the bijection between  Pre d r × Γ ⊢ r ⦂ A  and  Γ ⊢ r [ d ] A

TypingErasure : Set
TypingErasure = {Γ : List Ty} {r : Raw (length Γ)} {d : Mode} {A : Ty}
              → Γ ⊢ r [ d ] A  →  Pre d r

typingErasure : TypingErasure
typingErasure (var i refl) = ` L.index i
typingErasure (A ∋ t)   = A ∋ typingErasure t
typingErasure (t ↑ _)   = typingErasure t ↑
typingErasure (app t u) = app (typingErasure t) (typingErasure u)
typingErasure (abs t)   = abs (typingErasure t)

-- Implementing a type synthesiser using a bidirectional one

synthesise
  : ModePreprocessing → TypeSynthesis⇔
  → Soundness → Completeness
  → TypeSynthesis (¬_ ∘ Pre Syn)
synthesise pre syn⇔ s c Γ r with pre Syn r
... | yes p = inl (map′ (map₂ s) (map₂ (c p)) (syn⇔ Γ p))
... | no ¬p = inr ¬p

--   Γ ⊢ r ⦂ A   ←   Γ ⊢ r ⇒ A
--
--     ↑               ↑
--
--   r : Raw n   →   Pre Syn r

-- Strengthening bidirectionalisation

data Pre? : (valid exact : Bool) → Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ------------------------
        Pre? true true Syn (` i)

  _∋_ : (A : Ty)
      → Pre? v e    Chk      r
      → -----------------------
        Pre? v true Syn (A ∋ r)

  _↑  : Pre? v true  Syn r
      → ------------------
        Pre? v false Chk r

  ?∋_ : Pre? v     true  Chk r
      → ----------------------
        Pre? false false Syn r

  app : Pre? v₀ e₀ Syn r
      → Pre? v₁ e₁ Chk s
      → And (v₀ ∷ v₁ ∷ []) v
      → -------------------------
        Pre? v true Syn (app r s)

  abs : Pre? v e    Chk      r
      → -----------------------
        Pre? v true Chk (abs r)

app-abs : Pre? false true Syn {zero} (app (abs (` zero)) (abs (` zero)))
app-abs = app (?∋ abs ((` zero) ↑)) (abs ((` zero) ↑)) hd

toPre : Pre? true e d r → Pre d r
toPre (` i)   = ` i
toPre (A ∋ p) = A ∋ toPre p
toPre (p ↑)   = toPre p ↑
toPre (app p q (tl (tl nil))) = app (toPre p) (toPre q)
toPre (abs p) = abs (toPre p)

to¬Pre-Syn : Pre? v true Chk r → ¬ Pre Syn r
to¬Pre-Syn (abs p) ()

mutual

  to¬Pre-Chk : Pre? false true Syn r → ¬ Pre Chk r
  to¬Pre-Chk p (q ↑) = to¬Pre p q

  to¬Pre : Pre? false e d r → ¬ Pre d r
  to¬Pre (A ∋ p)            (.A ∋ q)   = to¬Pre p q
  to¬Pre (p ↑)              q          = to¬Pre-Chk p q
  to¬Pre (?∋ p)             q          = to¬Pre-Syn p q
  to¬Pre (app p p' hd)      (app q q') = to¬Pre p q
  to¬Pre (app p p' (tl hd)) (app q q') = to¬Pre p' q'
  to¬Pre (abs p)            (abs q)    = to¬Pre p q

ModePreprocessing? : Set
ModePreprocessing? =
  (d : Mode) {n : ℕ} (r : Raw n) → ∃[ v ] ∃[ e ] Pre? v e d r

ModePreprocessing-lemma : ModePreprocessing? → ModePreprocessing
ModePreprocessing-lemma pre? d r with pre? d r
... | false , _ , p = no (to¬Pre p)
... | true  , _ , p = yes (toPre p)

Classification : ∀ {n} → Raw n → Set
Classification r = Pre? true  true Syn r
          ⊎        Pre? true  true Chk r
          ⊎ ∃[ e ] Pre? false e    Chk r

adjustMode : (d : Mode) {r : Raw n}
           → Classification r → ∃[ v ] ∃[ e ] Pre? v e d r
adjustMode Chk (inl               p    ) = _ , _ ,    p ↑
adjustMode Syn (inl               p    ) = _ , _ ,    p
adjustMode Chk (inr (inl          p   )) = _ , _ ,    p
adjustMode Syn (inr (inl          p   )) = _ , _ , ?∋ p
adjustMode Chk (inr (inr (_     , p  ))) = _ , _ ,    p
adjustMode Syn (inr (inr (false , p ↑))) = _ , _ ,    p
adjustMode Syn (inr (inr (true  , p  ))) = _ , _ , ?∋ p

preprocess' : (r : Raw n) → Classification r
preprocess' (` i) = inl (` i)
preprocess' (A ∋ r) with adjustMode Chk (preprocess' r)
... | false , _ , p = inr (inr (_ , (A ∋ p) ↑))
... | true  , _ , p = inl (          A ∋ p    )
preprocess' (app r s) with adjustMode Syn (preprocess' r) | adjustMode Chk (preprocess' s)
... | false , _ , p | v     , _ , q = inr (inr (_ , app p q  hd        ↑))
... | true  , _ , p | false , _ , q = inr (inr (_ , app p q (tl  hd)   ↑))
... | true  , _ , p | true  , _ , q = inl (         app p q (tl (tl nil)))
preprocess' (abs r) with adjustMode Chk (preprocess' r)
... | false , _ , p = inr (inr (_ , abs p))
... | true  , _ , p = inr (inl (    abs p))

preprocess? : ModePreprocessing?
preprocess? d = adjustMode d ∘ preprocess'

infix 3 _≤ᴬ_

data _≤ᴬ_ : {n : ℕ} → Raw n → Raw n → Set where

  `_   : (i : Fin n)
       → --------------
         (` i) ≤ᴬ (` i)

  _∋_  : (A : Ty)
       → r ≤ᴬ r'
       → -------------------
         (A ∋ r) ≤ᴬ (A ∋ r')

  _∋⁺_ : (A : Ty)
       → r ≤ᴬ r'
       → -------------
         r ≤ᴬ (A ∋ r')

  app  : r ≤ᴬ r'
       → s ≤ᴬ s'
       → --------------------
         app r s ≤ᴬ app r' s'

  abs  : r ≤ᴬ r'
       → ---------------
         abs r ≤ᴬ abs r'

annotatability : Pre? v e d r  →  Γ ⊢ r ⦂ A  →  ∃[ r' ]  r ≤ᴬ r'  ×  Γ ⊢ r' [ d ] A
annotatability (` .(L.index i)) (` i) = _ , ` (L.index i) , var i refl
annotatability (p ↑) t with annotatability p t
... | _ , r≤r' , t' = _ , r≤r' , t' ↑ refl
annotatability (A ∋ p) (.A ∋ t) with annotatability p t
... | _ , r≤r' , t' = _ , A ∋ r≤r' , A ∋ t'
annotatability {A = A} (?∋ p) t with annotatability p t
... | _ , r≤r' , t' = _ , A ∋⁺ r≤r' , A ∋ t'
annotatability (app p q _) (app t u) with annotatability p t | annotatability q u
... | _ , r≤r' , t' | _ , s≤s' , u' = _ , app r≤r' s≤s' , app t' u'
annotatability (abs p) (abs t) with annotatability p t
... | _ , r≤r' , t' = _ , abs r≤r' , abs t'
