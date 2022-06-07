open import Prelude

import Syntax.Simple.Description     as S
open import Syntax.Typed.Description as T

module Syntax.Typed.Term {SD : S.Desc} (D : Desc {SD}) where
open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T)
open import Syntax.Context T

private
  variable
    A B   : T
    Γ Δ Ξ : Ctx

infix 40 `_

data Tm : Fam₀ where
  `_ : _∈_       ⇒ Tm 
  op : ⟦ D ⟧ Tm  ⇒ Tm 

mutual
  rename : Ren Γ Δ 
    → Tm A Γ → Tm A Δ
  rename f (`  x) = ` f x
  rename f (op t) = op (renameMap _ f t)

  renameMap : ∀ D
    → Ren Γ Δ 
    → (⟦ D ⟧ Tm) A Γ → (⟦ D ⟧ Tm) A Δ
  renameMap (D ∷ _)  f (inl t) = inl (renameMapᶜ D f t)
  renameMap (_ ∷ Ds) f (inr t) = inr (renameMap Ds f t)

  renameMapᶜ : (D : ConD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᶜ Tm) A Γ → (⟦ D ⟧ᶜ Tm) A Δ
  renameMapᶜ (ι A D) f (eq , ts) = eq , renameMapᵃˢ D f ts
  renameMapᶜ (σ D)   f (_ , t)   = _ , renameMapᶜ (D _) f t

  renameMapᵃˢ : (D : ArgsD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) Γ → (⟦ D ⟧ᵃˢ Tm) Δ
  renameMapᵃˢ ι        f _        = _
  renameMapᵃˢ (ρ D Ds) f (t , ts) = renameMapᵃ D f t , renameMapᵃˢ Ds f ts

  renameMapᵃ : (D : ArgD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃ Tm) Γ → (⟦ D ⟧ᵃ Tm) Δ
  renameMapᵃ (⊢ B)   f t = rename f t
  renameMapᵃ (A ∙ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Ctx) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f zero    = ` zero
exts f (suc x) = rename suc (f x)

mutual
  subst : Sub Γ Δ
    → ∀ {A} → Tm A Γ → Tm A Δ
  subst f (` x)  = f x
  subst f (op t) = op (substMap _ f t)

  substMap : ∀ D
    → Sub Γ Δ 
    → (⟦ D ⟧ Tm) A Γ → (⟦ D ⟧ Tm) A Δ
  substMap (D ∷ Ds) f (inl x) = inl (substMapᶜ D f x)
  substMap (D ∷ Ds) f (inr y) = inr (substMap Ds f y)

  substMapᶜ : (D : ConD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᶜ Tm) A Γ → (⟦ D ⟧ᶜ Tm) A Δ
  substMapᶜ (ι A D) f (eq , ts) = eq , substMapᵃˢ D f ts
  substMapᶜ (σ D)   f (_  , ts) = _  , substMapᶜ (D _) f ts

  substMapᵃˢ : (D : ArgsD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) Γ → (⟦ D ⟧ᵃˢ Tm) Δ
  substMapᵃˢ ι        f _        = _
  substMapᵃˢ (ρ D Ds) f (t , ts) = substMapᵃ D f t , substMapᵃˢ Ds f ts

  substMapᵃ : (D : ArgD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃ Tm) Γ → (⟦ D ⟧ᵃ Tm) Δ
  substMapᵃ (⊢ B)   f t = subst f t
  substMapᵃ (A ∙ Δ) f t = substMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟪ f ⟫ t = subst f t

module _ {X : Fam ℓ} (α : (D -Alg) X) where mutual
  fold : Tm ⇒ X
  fold (` x)  = α .var x -- α .var x
  fold (op t) = α .alg (foldMap _ t)

  foldMap : ∀ D
    → ⟦ D ⟧ Tm ⇒ ⟦ D ⟧ X
  foldMap (D ∷ Ds) (inl t) = inl (foldMapᶜ D t)
  foldMap (D ∷ Ds) (inr t) = inr (foldMap Ds t)

  foldMapᶜ : ∀ (D : ConD Ξ)
    → ⟦ D ⟧ᶜ Tm ⇒ ⟦ D ⟧ᶜ X
  foldMapᶜ (ι A D) (eq , t) = eq , foldMapᵃˢ D t
  foldMapᶜ (σ D)   (A , t)  = A , foldMapᶜ (D A) t

  foldMapᵃˢ : ∀ (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ Tm ⇒₁ ⟦ D ⟧ᵃˢ X
  foldMapᵃˢ ι        _        = _
  foldMapᵃˢ (ρ D Ds) (t , ts) = foldMapᵃ D t , foldMapᵃˢ Ds ts

  foldMapᵃ : ∀ (D : ArgD Ξ)
    → ⟦ D ⟧ᵃ Tm ⇒₁ ⟦ D ⟧ᵃ X
  foldMapᵃ (⊢ B)   t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t
