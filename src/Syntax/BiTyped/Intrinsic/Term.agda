open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as T

module Syntax.BiTyped.Intrinsic.Term {SD : S.Desc} (D : T.Desc {SD}) where

open import Syntax.Simple.Term SD
  using (Sub₀) renaming (Tm₀ to T; Tm to TExp; Sub to TSub)
open import Syntax.Context
open T {SD}
open import Syntax.BiTyped.Intrinsic.Functor {SD}

private
  variable
    m     : Mode
    Ξ     : ℕ
    σ     : Sub₀ Ξ
    A B   : T
    Γ Δ   : Ctx T

infix 9 `_

data Tm : Fam₀ where
  `_ : _∈_ ⇒ Tm Infer
  _∋_
    : (A : T) (t : Tm Check A Γ)
    → Tm Infer A Γ
  ⇉_by_ : (t : Tm Infer A Γ) (eq : A ≡ B)
    → Tm Check B Γ
  op : (⟦ D ⟧ Tm) m ⇒ Tm m

Tm⇉ = Tm Infer
Tm⇇ = Tm Check

mutual
  rename : Ren Γ Δ 
    → Tm m A Γ → Tm m A Δ
  rename f (`  x)                        = ` f x
  rename f (A ∋ t)                       = A ∋ rename f t
  rename f (⇉ t by eq)                   = ⇉ (rename f t) by eq
  rename f (op (D , x , p , σ , q , ts)) =
    op (D , x , p , σ , q , renameMap _ f ts)

  renameMap : (D : ArgsD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  renameMap ∅        f _        = _
  renameMap (D ∙ Ds) f (t , ts) = renameMapᵃ D f t , renameMap Ds f ts

  renameMapᵃ : (D : ArgD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  renameMapᵃ (ι m B) f t = rename f t
  renameMapᵃ (A ∙ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Ctx T) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm Infer A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

extsⁿ : {Ξ : Ctx T}
  → Sub Γ Δ → Sub (Ξ ++ Γ) (Ξ ++ Δ)
extsⁿ {Ξ = ∅}     f x         = f x
extsⁿ {Ξ = A ∙ Ξ} f (here px) = ` here px
extsⁿ {Ξ = A ∙ Ξ} f (there x) = rename there (extsⁿ f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm m A Γ → Tm m A Δ
  sub f (` x)                         = f x
  sub f (A ∋ t)                       = A ∋ sub f t
  sub f (⇉ t by eq)                   = ⇉ (sub f t) by eq
  sub f (op (D , x , p , σ , q , ts)) =
    op (D , x , p , σ , q , subMap _ f ts)

  subMap : (D : ArgsD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  subMap ∅        f _        = _
  subMap (D ∙ Ds) f (t , ts) = subMapᵃ D f t , subMap Ds f ts

  subMapᵃ : (D : ArgD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  subMapᵃ (ι m B) f t = sub f t
  subMapᵃ (A ∙ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam ℓ} (α : (D -Alg) X) where mutual
  fold : Tm m ⇒ X m
  fold (` x)         = α .var x -- α .var x
  fold (A ∋ t)       = α .toInfer (fold t)
  fold (⇉ t by refl) = α .toCheck (fold t)
  fold (op (D , x , p , σ , q , ts)) = α .alg (D , x , p , σ , q , foldMap (ConD.args D) ts)

  foldMap : ∀ (D : ArgsD Ξ)
    → (⟦ D ⟧ᵃˢ Tm) σ ⇒₁ (⟦ D ⟧ᵃˢ X) σ
  foldMap ∅        _        = _
  foldMap (D ∙ Ds) (t , ts) = foldMapᵃ D t , foldMap Ds ts

  foldMapᵃ : ∀ (D : ArgD Ξ)
    → (⟦ D ⟧ᵃ Tm) σ ⇒₁ (⟦ D ⟧ᵃ X) σ
  foldMapᵃ (ι m B) t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t