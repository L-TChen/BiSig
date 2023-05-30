{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as T

module Syntax.BiTyped.Intrinsic.Term {SD : S.Desc} (D : T.Desc SD) where

open T SD

open import Syntax.Simple  SD
  using (TExp; TExps; TSub) 
open import Syntax.Context SD

open import Syntax.BiTyped.Intrinsic.Functor {SD}

private
  variable
    d     : Mode
    Θ Ξ   : ℕ
    ρ     : TSub Ξ Θ
    A B C : TExp Θ
    Γ Γ′ Δ   : Cxt  Θ

infix 9 `_

data Tm (Θ : ℕ) : Fam₀ Θ where
  `_ : _∈_ ⇒ Tm Θ Inf
  _∋_
    : (A : TExp Θ) (t : Tm Θ Chk A Γ)
    → Tm Θ Inf A Γ
  ⇉_by_ : (t : Tm Θ Inf A Γ) (eq : B ≡ A)
    → Tm Θ Chk B Γ
  op : ⟦ D ⟧ (Tm Θ) d ⇒ Tm Θ d

Tm⇒ Tm⇐ : (Θ : ℕ) → _
Tm⇒ Θ = Tm Θ Inf
Tm⇐ Θ = Tm Θ Chk

mutual
  rename : Ren Γ Δ
    → Tm Θ d A Γ → Tm Θ d A Δ
  rename f (`  x)                    = ` f x
  rename f (A ∋ t)                   = A ∋ rename f t
  rename f (⇉ t by eq)               = ⇉ rename f t by eq
  rename f (op (i , p , σ , q , ts)) = op (i , p , σ , q , renameMap _ f ts)

  renameMap : (D : ArgsD Ξ)
    → Ren Γ Δ
    → ⟦ D ⟧ᵃˢ (Tm Θ) ρ Γ → ⟦ D ⟧ᵃˢ (Tm Θ) ρ Δ
  renameMap []                 f _        = _
  renameMap (Θ ⊢[ _ ] _ ∷ Ds) f (t , ts) = renameMapᵃ Θ f t , renameMap Ds f ts

  renameMapᵃ : (Δ : TExps Ξ)
    → Ren Γ Γ′
    → ⟦ Δ ⟧ᵃ (Tm Θ d A) ρ Γ → ⟦ Δ ⟧ᵃ (Tm Θ d A) ρ Γ′
  renameMapᵃ []      f t = rename f t
  renameMapᵃ (A ∷ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm Θ d A Γ → Tm Θ d A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Cxt Θ) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm _ Inf A Δ

exts : Sub Γ Δ → Sub (A ∷ Γ) (A ∷ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

extsⁿ : {Ξ : Cxt Θ}
  → Sub Γ Δ → Sub (Ξ ++ Γ) (Ξ ++ Δ)
extsⁿ {Ξ = []}     f x         = f x
extsⁿ {Ξ = A ∷ Ξ} f (here px) = ` here px
extsⁿ {Ξ = A ∷ Ξ} f (there x) = rename there (extsⁿ f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm Θ d A Γ → Tm Θ d A Δ
  sub f (` x)                     = f x
  sub f (A ∋ t)                   = A ∋ sub f t
  sub f (⇉ t by eq)               = ⇉ (sub f t) by eq
  sub f (op (i , p , σ , q , ts)) =
    op (i , p , σ , q , subMap _ f ts)

  subMap : (D : ArgsD Ξ)
    → Sub Γ Γ′
    → ⟦ D ⟧ᵃˢ (Tm Θ) ρ Γ → ⟦ D ⟧ᵃˢ (Tm Θ) ρ Γ′
  subMap []                f _        = _
  subMap (Θ ⊢[ _ ] _ ∷ Ds) f (t , ts) = subMapᵃ Θ f t , subMap Ds f ts

  subMapᵃ : (Δ : TExps Ξ)
    → Sub Γ Γ′
    → ⟦ Δ ⟧ᵃ (Tm Θ d A) ρ Γ → ⟦ Δ ⟧ᵃ (Tm Θ d A) ρ Γ′
  subMapᵃ []      f t = sub f t
  subMapᵃ (A ∷ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm Θ d A Γ → Tm Θ d A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam Θ ℓ} (α : (D -Alg) X) where mutual
  fold : Tm Θ d ⇒ X d
  fold (` x)         = α .var x
  fold (A ∋ t)       = α .toInf (fold t)
  fold (⇉ t by refl) = α .toChk (fold t)
  fold (op (i , p , σ , q , ts)) = α .alg (i , p , σ , q , foldMap _ ts)

  foldMap : (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ (Tm Θ) ρ ⇒₁ ⟦ D ⟧ᵃˢ X ρ
  foldMap []        _                = _
  foldMap (Θ ⊢[ _ ] _ ∷ Ds) (t , ts) = foldMapᵃ Θ t , foldMap Ds ts

  foldMapᵃ : (Δ : TExps Ξ)
    → ⟦ Δ ⟧ᵃ (Tm Θ d A) ρ ⇒₁ ⟦ Δ ⟧ᵃ (X d A) ρ
  foldMapᵃ []      t = fold t
  foldMapᵃ (A ∷ Δ) t = foldMapᵃ Δ t
