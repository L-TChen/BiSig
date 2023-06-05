{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Term {SD : S.Desc} (D : T.Desc SD) where

open import Syntax.Simple SD
  using (TExp; TExps; TSub)

open import Syntax.Context            SD
open import Syntax.Typed.Intrinsic.Functor {SD}

open T SD

private variable
    Ξ Θ    : ℕ
    A B    : TExp Θ
    Γ Δ Γ′ : Cxt Θ
    σ      : TSub Ξ Θ

-- Tm m A Γ = Γ ⊢ A

infix 9 `_
data Tm (Θ : ℕ) : TExp Θ → Cxt Θ → Set where
  `_ : _∈_          ⇒ Tm Θ
  op : ⟦ D ⟧ (Tm Θ) ⇒ Tm Θ

mutual
  rename : Ren Γ Δ
    → Tm Θ A Γ → Tm Θ A Δ
  rename f (`  x)                = ` f x
  rename f (op (i , σ , p , ts)) = op (i , σ , p , renameMap _ f ts)

  renameMap : (D : ArgsD Ξ)
    → Ren Γ Δ
    → ⟦ D ⟧ᵃˢ (Tm Θ) σ Γ → ⟦ D ⟧ᵃˢ (Tm Θ) σ Δ
  renameMap []           f _        = tt
  renameMap (Θ ⊢ C ∷ Ds) f (t , ts) = renameMapᵃ Θ f t , renameMap Ds f ts

  renameMapᵃ : (Δ : TExps Ξ)
    → Ren Γ Γ′
    → ⟦ Δ ⟧ᵃ (Tm Θ A) σ Γ → ⟦ Δ ⟧ᵃ (Tm Θ A) σ Γ′
  renameMapᵃ []      f t = rename f t
  renameMapᵃ (A ∷ Θ) f t = renameMapᵃ Θ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Γ′
  → ∀ {A} → Tm Θ A Γ → Tm Θ A Γ′
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Cxt Θ) → Set
Sub Γ Δ = {A : TExp _} (x : A ∈ Γ) → Tm _ A Δ

exts : Sub Γ Δ → Sub (A ∷ Γ) (A ∷ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm Θ A Γ → Tm Θ A Δ
  sub f (` x)                  = f x
  sub f (op (i , σ , eq , ts)) = op (i , σ , eq , subMap _ f ts)

  subMap : (D : ArgsD Ξ)
    → Sub Γ Δ
    → ⟦ D ⟧ᵃˢ (Tm Θ) σ Γ → ⟦ D ⟧ᵃˢ (Tm Θ) σ Δ
  subMap []           f _        = _
  subMap (Θ ⊢ C ∷ Ds) f (t , ts) = subMapᵃ Θ f t , subMap Ds f ts

  subMapᵃ : (Δ : TExps Ξ)
    → Sub Γ Γ′
    → ⟦ Δ ⟧ᵃ (Tm Θ A) σ Γ → ⟦ Δ ⟧ᵃ (Tm Θ A) σ Γ′
  subMapᵃ []      f t = sub f t
  subMapᵃ (A ∷ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm Θ A Γ → Tm Θ A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam ℓ Θ} (α : (D -Alg) X) where mutual
  fold : Tm Θ ⇒ X
  fold (` x)                  = α .var x
  fold (op (i , σ , eq , ts)) = α .alg (i , σ , eq , foldMap _ ts)

  foldMap : (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ (Tm Θ) ⇒ ⟦ D ⟧ᵃˢ X
  foldMap []           _        = _
  foldMap (Θ ⊢ C ∷ Ds) (t , ts) = foldMapᵃ Θ t , foldMap Ds ts

  foldMapᵃ : (Δ : TExps Ξ)
    → ⟦ Δ ⟧ᵃ (Tm Θ A) ⇒ ⟦ Δ ⟧ᵃ (X A)
  foldMapᵃ []      t = fold t
  foldMapᵃ (A ∷ Δ) t = foldMapᵃ Δ t
