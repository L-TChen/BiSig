open import Prelude

import Syntax.Simple.Description     as S
open import Syntax.Typed.Description as T

module Syntax.Typed.Intrinsic.Term {SD : S.Desc} (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T; Tm to TExp; Sub to TSub)

open import Syntax.Context
open import Syntax.Typed.Intrinsic.Functor {SD}

private
  variable
    A B   : T
    Ξ     : ℕ
    Γ Δ   : Ctx T
    σ     : TSub Ξ 0

infix 9 `_
data Tm : Fam₀ where
  `_ : _∈_       ⇒ Tm
  op : ⟦ D ⟧ Tm  ⇒ Tm 

mutual
  rename : Ren Γ Δ 
    → Tm A Γ → Tm A Δ
  rename f (`  x) = ` f x
  rename f (op (D , x , σ , p , ts)) = op (_ , x , σ , p , renameMap (ConD.args D) f ts)

  renameMap : (D : ArgsD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  renameMap ι        f _        = _
  renameMap (ρ D Ds) f (t , ts) = renameMapᵃ D f t , renameMap Ds f ts

  renameMapᵃ : (D : ArgD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  renameMapᵃ (⊢ B)   f t = rename f t
  renameMapᵃ (A ∙ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Ctx T) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm A Γ → Tm A Δ
  sub f (` x)  = f x
  sub f (op (D , x , σ , eq , ts)) =
    op (_ , x , σ , eq , subMap (ConD.args D) f ts)

  subMap : (D : ArgsD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  subMap ι        f _        = _
  subMap (ρ D Ds) f (t , ts) = subMapᵃ D f t , subMap Ds f ts

  subMapᵃ : (D : ArgD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  subMapᵃ (⊢ B)   f t = sub f t
  subMapᵃ (A ∙ Δ) f t = subMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟪ f ⟫ t = sub f t

module _ {X : Fam ℓ} (α : (D -Alg) X) where mutual
  fold : Tm ⇒ X
  fold (` x)  = α .var x -- α .var x
  fold (op (D , x , σ , eq , ts)) =
    α . alg $ D , x , σ , eq , foldMap (ConD.args D) ts

  foldMap : ∀ (D : ArgsD Ξ)
    → (⟦ D ⟧ᵃˢ Tm) σ ⇒₁ (⟦ D ⟧ᵃˢ X) σ
  foldMap ι        _        = _
  foldMap (ρ D Ds) (t , ts) = foldMapᵃ D t , foldMap Ds ts

  foldMapᵃ : ∀ (D : ArgD Ξ)
    → (⟦ D ⟧ᵃ Tm) σ  ⇒₁ (⟦ D ⟧ᵃ X) σ
  foldMapᵃ (⊢ B)   t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t
