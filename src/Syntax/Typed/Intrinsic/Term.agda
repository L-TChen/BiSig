open import Prelude

import Syntax.Simple.Description     as S
open import Syntax.Typed.Description as T

module Syntax.Typed.Intrinsic.Term {SD : S.Desc} (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  using (Sub₀) renaming (Tm₀ to T; Tm to TExp; Tms to TExps)

open import Syntax.Context
open import Syntax.Typed.Intrinsic.Functor {SD}

private
  variable
    A B   : T
    Ξ     : ℕ
    Γ Δ   : Ctx T
    σ     : Sub₀ Ξ

infix 9 `_
data Tm : Fam₀ where
  `_ : _∈_       ⇒ Tm
  op : ⟦ D ⟧ Tm  ⇒ Tm 

mutual
  rename : Ren Γ Δ 
    → Tm A Γ → Tm A Δ
  rename f (`  x) = ` f x
  rename f (op (ι A D , x , σ , p , ts)) = op (_ , x , σ , p , renameMap D f ts)

  renameMap : (D : ArgsD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  renameMap ∅            f _        = _
  renameMap (Θ ⊢ C ∙ Ds) f (t , ts) = renameMapᵃ Θ f t , renameMap Ds f ts

  renameMapᵃ : (Θ : TExps Ξ)
    → Ren Γ Δ
    → (⟦ Θ ⟧ᵃ Tm A) σ Γ → (⟦ Θ ⟧ᵃ Tm A) σ Δ
  renameMapᵃ ∅       f t = rename f t
  renameMapᵃ (A ∙ Θ) f t = renameMapᵃ Θ (ext f) t
  -- renamemapᵃ (δ ⊢ b) f t = rename (extⁿ f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Ctx T) → Set
Sub Γ Δ = {A : T} (x : A ∈ Γ) → Tm A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f (here px) = ` here px
exts f (there x) = rename there (f x)

extsⁿ : {Ξ : Ctx T}
  → Sub Γ Δ → Sub (Ξ ++ Γ) (Ξ ++ Δ)
extsⁿ {Ξ = ∅}     f i = f i
extsⁿ {Ξ = A ∙ Ξ} f (here px) = ` here px
extsⁿ {Ξ = A ∙ Ξ} f (there i) = ⟨ there ⟩ extsⁿ f i

mutual
  sub : Sub Γ Δ
    → ∀ {A} → Tm A Γ → Tm A Δ
  sub f (` x)                      = f x
  sub f (op (D , x , σ , eq , ts)) =
    op (_ , x , σ , eq , subMap (ConD.args D) f ts)

  subMap : (D : ArgsD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  subMap ∅            f _        = _
  subMap (Θ ⊢ C ∙ Ds) f (t , ts) = subMapᵃ Θ f t , subMap Ds f ts

  subMapᵃ : (Θ : TExps Ξ)
    → Sub Γ Δ
    → (⟦ Θ ⟧ᵃ Tm A) σ Γ → (⟦ Θ ⟧ᵃ Tm A) σ Δ
  -- subMapᵃ (Ξ ⊢ B) f t = sub (extsⁿ f) t
  subMapᵃ ∅       f t = sub f t
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

  foldMap : (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ Tm ⇒ ⟦ D ⟧ᵃˢ X
  foldMap ∅            _        = _
  foldMap (Θ ⊢ C ∙ Ds) (t , ts) = foldMapᵃ Θ t , foldMap Ds ts

  foldMapᵃ : (Θ : TExps Ξ)
    → ⟦ Θ ⟧ᵃ Tm A ⇒ ⟦ Θ ⟧ᵃ X A
  -- foldMapᵃ (Δ ⊢ B) t = fold t
  foldMapᵃ ∅       t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t
