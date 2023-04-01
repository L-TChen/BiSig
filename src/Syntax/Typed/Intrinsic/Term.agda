{-# OPTIONS --safe #-} 

open import Prelude

import Syntax.Simple.Description     as S
open import Syntax.Typed.Description as T

module Syntax.Typed.Intrinsic.Term {SD : S.Desc} (D : Desc {SD}) where

open import Syntax.Simple.Term        SD
  using () renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Simple.Association SD

open import Syntax.Context            SD
open import Syntax.Typed.Intrinsic.Functor {SD}

private variable
    n m   : ℕ
    A B   : TExp m
    Γ Δ   : Cxt m
    σ     : TSub n m

-- Tm m A Γ = Γ ⊢ A

infix 9 `_
data Tm (m : ℕ) : TExp m → Cxt m → Set where
  `_ : _∈_          ⇒ Tm m
  op : ⟦ D ⟧ (Tm m) ⇒ Tm m

mutual
  rename : Ren Γ Δ
    → Tm m A Γ → Tm m A Δ
  rename f (`  x)                         = ` f x
  rename f (op (ι B Ds , x , σ , p , ts)) = op (_ , x , σ , p , renameMap Ds f ts)

  renameMap : (D : ArgsD n)
    → Ren Γ Δ
    → ⟦ D ⟧ᵃˢ (Tm m) σ Γ → ⟦ D ⟧ᵃˢ (Tm m) σ Δ
  renameMap []            f _        = tt
  renameMap (Θ ⊢ C ∷ Ds) f (t , ts) = renameMapᵃ Θ f t , renameMap Ds f ts

  renameMapᵃ : (Θ : TExps n)
    → Ren Γ Δ
    → ⟦ Θ ⟧ᵃ (Tm m A) σ Γ → ⟦ Θ ⟧ᵃ (Tm m A) σ Δ
  renameMapᵃ []       f t = rename f t
  renameMapᵃ (A ∷ Θ) f t = renameMapᵃ Θ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Cxt m) → Set
Sub Γ Δ = {A : TExp _} (x : A ∈ Γ) → Tm _ A Δ

exts : Sub Γ Δ → Sub (A ∷ Γ) (A ∷ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm m A Γ → Tm m A Δ
  sub f (` x)                      = f x
  sub f (op (ι B Ds , x , σ , eq , ts)) =
    op (_ , x , σ , eq , subMap Ds f ts)

  subMap : (D : ArgsD n)
    → Sub Γ Δ
    → ⟦ D ⟧ᵃˢ (Tm m) σ Γ → ⟦ D ⟧ᵃˢ (Tm m) σ Δ
  subMap []            f _        = _
  subMap (Θ ⊢ C ∷ Ds) f (t , ts) = subMapᵃ Θ f t , subMap Ds f ts

  subMapᵃ : (Θ : TExps n)
    → Sub Γ Δ
    → ⟦ Θ ⟧ᵃ (Tm m A) σ Γ → ⟦ Θ ⟧ᵃ (Tm m A) σ Δ
  subMapᵃ []       f t = sub f t
  subMapᵃ (A ∷ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam ℓ m} (α : (D -Alg) X) where mutual
  fold : Tm m ⇒ X
  fold (` x)  = α .var x
  fold (op (D , x , σ , eq , ts)) =
    α . alg $ D , x , σ , eq , foldMap (ConD.args D) ts

  foldMap : (D : ArgsD n)
    → ⟦ D ⟧ᵃˢ (Tm m) ⇒ ⟦ D ⟧ᵃˢ X
  foldMap []            _        = _
  foldMap (Θ ⊢ C ∷ Ds) (t , ts) = foldMapᵃ Θ t , foldMap Ds ts

  foldMapᵃ : (Θ : TExps n)
    → ⟦ Θ ⟧ᵃ (Tm m A) ⇒ ⟦ Θ ⟧ᵃ (X A)
  foldMapᵃ []       t = fold t
  foldMapᵃ (A ∷ Δ) t = foldMapᵃ Δ t
