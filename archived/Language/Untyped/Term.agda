open import Prelude

module Language.Untyped.Term where

open import Language.Type
  using (_⁺; z; s_)
  
infixr 5 ƛ_
infixl 7 _·_
infixr 8 ⟪_⟫_ ⟨_⟩_
infixr 9 `_ -- #_

data Λ (X : Type) : Type where
  `_
    : (x : X)
    → Λ X
  _·_
    : Λ X → Λ X
    → Λ X
  ƛ_
    : Λ (X ⁺)
    → Λ X

private
  variable
    Γ Δ : Type
Ren : (Γ Δ : Type) → Type
Ren Γ Δ = Δ → Γ

ext : ∀ {Γ Δ}
  → Ren Γ Δ → Ren (Γ ⁺) (Δ ⁺)
ext ρ z     = z
ext ρ (s x) = s (ρ x)

⟨_⟩_ : ∀ {Γ Δ}
  → (Δ → Γ) → Λ Δ → Λ Γ
⟨ ρ ⟩ (` x)   = ` ρ x
⟨ ρ ⟩ (t · u) = ⟨ ρ ⟩ t · ⟨ ρ ⟩ u
⟨ ρ ⟩ (ƛ t)   = ƛ ⟨ ext ρ ⟩ t

Sub : (Γ Δ : Type) → Type
Sub Γ Δ = Δ → Λ Γ

exts : ∀ {Γ Δ}
  → Sub Γ Δ → Sub (Γ ⁺) (Δ ⁺)
exts σ z     = ` z
exts σ (s x) = ⟨ s_ ⟩ σ x

⟪_⟫_
  : ∀ {Δ Γ}
  → (Δ   → Λ Γ)
  → (Λ Δ → Λ Γ)
⟪ σ ⟫ (` x)   = σ x
⟪ σ ⟫ (t · u) = ⟪ σ ⟫ t · ⟪ σ ⟫ u
⟪ σ ⟫ (ƛ t)   = ƛ ⟪ exts σ ⟫ t

_⨟_
  : {Z : Type}
  → Sub Γ Δ → Sub Δ Z → Sub Γ Z
(σ ⨟ σ′) x = ⟪ σ ⟫ σ′ x

⇑_ : Ren Γ Δ → Sub Γ Δ
(⇑ ρ) x = ` ρ x

subst-idR : (σ : Sub Γ Δ)
  → (x : Δ)
  → ⟪ σ ⟫ (` x) ≡ σ x
subst-idR σ x = refl

exts-ids=ids
  : (x : (Γ ⁺))
  → exts `_ x ≡ ` x
exts-ids=ids z     = refl
exts-ids=ids (s x) = refl

subst-idL : (t : Λ Γ)
  → ⟪ `_ ⟫ t ≡ t
subst-idL (` x)   = refl
subst-idL (t · u) = cong₂ _·_ (subst-idL t) (subst-idL u)
subst-idL (ƛ t)   = cong ƛ_ (
  ⟪ exts `_ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-ids=ids x i) ⟫ t ⟩
  ⟪ `_ ⟫ t
    ≡⟨ subst-idL t ⟩
  t ∎)
  where open ≡-Reasoning

-- tedious to prove
ren-exts : (σ : Sub Γ Δ)
  → (t : Λ Δ)
  → ⟪ exts σ ⟫ ⟨ s_ ⟩ t ≡ ⟨ s_ ⟩ ⟪ σ ⟫ t
ren-exts σ (` x)   = refl
ren-exts σ (t · u) = cong₂ _·_ (ren-exts σ t) (ren-exts σ u)
ren-exts σ (ƛ t)   = cong ƛ_ {!ren-exts (exts σ) t!}

exts-comp : {Z : Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (x : (Z ⁺))
  → (exts σ ⨟ exts σ′) x ≡ exts (σ ⨟ σ′) x
exts-comp σ σ′ z     = refl
exts-comp σ σ′ (s x) = begin
  (exts σ ⨟ exts σ′) (s x)
    ≡⟨ refl ⟩
  ⟪ exts σ ⟫ ⟨ s_ ⟩ (σ′ x)
    ≡⟨ ren-exts σ (σ′ x) ⟩
  ⟨ s_ ⟩ ⟪ σ ⟫ (σ′ x)
    ≡⟨ refl ⟩
  exts (σ ⨟ σ′) (s x) ∎
  where open ≡-Reasoning

subst-assoc
  : {Z : Type}
  → (σ : Sub Γ Δ) (σ′ : Sub Δ Z)
  → (t : Λ Z)
  → ⟪ σ ⟫ ⟪ σ′ ⟫ t ≡ ⟪ σ ⨟ σ′ ⟫ t
subst-assoc σ σ′ (` x)   = refl
subst-assoc σ σ′ (t · u) = cong₂ _·_
  (subst-assoc σ σ′ t) (subst-assoc σ σ′ u)
subst-assoc σ σ′ (ƛ t)   = cong ƛ_
  (⟪ exts σ ⟫ ⟪ exts σ′ ⟫ t
    ≡⟨ subst-assoc (exts σ) (exts σ′) t ⟩
  ⟪ exts σ ⨟ exts σ′ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → exts-comp σ σ′ x i) ⟫ t ⟩
   ⟪ exts (σ ⨟ σ′) ⟫ t ∎)
  where open ≡-Reasoning

open import Category.Kleisli
open import Category.Kleisli.Continuation
open Monad ⦃...⦄

extB : (Γ → Bool) → Γ ⁺ → Bool
extB ρ z     = true
extB ρ (s x) = ρ x

ƛall : Cont Bool (Γ ⁺)
  → Cont Bool Γ
ƛall k .runCont ρ = k .runCont (extB ρ)
{-
ƛall-natural : (ρ : Γ → Δ) (k : Cont Bool (Γ ⁺)) 
  → {!!}
ƛall-natural ρ k = {!!}
-}

·all : (k₁ k₂ : Cont Bool Γ)
  → Cont Bool Γ
·all k₁ k₂ .runCont ρ = (k₁ .runCont ρ) and k₂ .runCont ρ

`all : Γ
  → Cont Bool Γ
`all = return

Λall : Λ Γ → Cont Bool Γ
Λall (` x)   = return x
Λall (t · u) = ·all (Λall t) (Λall u)
Λall (ƛ t)   = ƛall (Λall t)

{-
all : Λ Γ → Cont Bool Γ
all (` x)   .runCont ρ = ρ x
all (t · u) .runCont ρ = all t .runCont ρ and all u .runCont ρ
all (ƛ t)   .runCont ρ = all t .runCont (extB ρ)
-}

all : Λ Γ → ((Γ → Bool) → Bool)
all (` x) ρ   = ρ x
all (t · u) ρ = all t ρ and all u ρ
all (ƛ t) ρ   = all t (extB ρ)

↑_ : (Γ → Δ) → (Γ → Λ Δ)
↑ ρ = `_ ∘ ρ

↑-ext : (ρ : Γ → Δ)
  → ∀ x
  → (↑ (ext ρ)) x ≡ exts (↑ ρ) x
↑-ext ρ z     = refl
↑-ext ρ (s x) = refl

ren : (ρ : Γ → Δ) (t : Λ Γ)
  → ⟨ ρ ⟩ t ≡ ⟪ ↑ ρ ⟫ t
ren ρ (` x)   = refl
ren ρ (t · u) = cong₂ _·_ (ren ρ t) (ren ρ u)
ren ρ (ƛ t)   = cong ƛ_ (begin
  ⟨ ext ρ ⟩ t
    ≡⟨ ren (ext ρ) t ⟩
  ⟪ ↑ ext ρ ⟫ t
    ≡[ i ]⟨ ⟪ (λ x → ↑-ext ρ x i) ⟫ t ⟩
  ⟪ exts (↑ ρ) ⟫ t ∎)
  where open ≡-Reasoning

renaming-all-lem
  : (σ : Γ → Δ) (t : Λ Γ) (ρ : Δ → Bool) 
  → all (⟨ σ ⟩ t) ρ ≡ all t (λ x → all (` σ x) ρ)
renaming-all-lem σ (` x)   ρ = refl
renaming-all-lem σ (t · u) ρ = cong₂ _and_ (renaming-all-lem σ t ρ) (renaming-all-lem σ u ρ)
renaming-all-lem σ (ƛ t)   ρ = begin
  all (⟨ σ ⟩ (ƛ t)) ρ
    ≡⟨ refl ⟩
  all (⟨ ext σ ⟩ t) (extB ρ)
    ≡⟨ renaming-all-lem (ext σ) t (extB ρ) ⟩
  all t (λ x → all (` (ext σ x)) (extB ρ))
    ≡⟨ cong (all t) (funExt lem) ⟩
  all t (extB (λ x → ρ (σ x)))
    ∎
  where
    open ≡-Reasoning
    lem : ∀ x → extB ρ (ext σ x) ≡ extB (λ x → ρ (σ x)) x
    lem z     = refl
    lem (s x) = refl

subst-all-lem
  : (σ : Γ → Λ Δ) (t : Λ Γ) (ρ : Δ → Bool) 
  → all (⟪ σ ⟫ t) ρ ≡ all t (λ x → all (σ x) ρ)
  -- _=<<_  ContMonad f k .runCont ρ = k .runCont λ x → f x .runCont ρ
subst-all-lem σ (` x)   ρ = refl
subst-all-lem σ (t · u) ρ = cong₂ _and_
  (subst-all-lem σ t ρ) (subst-all-lem σ u ρ)
subst-all-lem σ (ƛ t)   ρ = begin
  all (⟪ exts σ ⟫ t) (extB ρ)
    ≡⟨ subst-all-lem (exts σ) t (extB ρ) ⟩
  all t (λ x → all ((exts σ) x) (extB ρ))
    ≡⟨ cong (all t) (funExt lem) ⟩
  all t (extB (λ x → all (σ x) ρ)) ∎
  where
    open ≡-Reasoning
    lem : ∀ x → all ((exts σ x)) (extB ρ) ≡ (extB (λ x → all (σ x) ρ)) x
    lem z     = refl
    lem (s x) = begin
      all (⟨ s_ ⟩ σ x) (extB ρ)
        ≡⟨ renaming-all-lem s_ (σ x) (extB ρ) ⟩
      all (σ x) ρ
        ∎
      
