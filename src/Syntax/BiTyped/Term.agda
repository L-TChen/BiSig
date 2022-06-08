open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as T

module Syntax.BiTyped.Term {SD : S.Desc} (D : T.Desc {SD}) where
open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T; Tm to TExp; Sub to TSub)
open import Syntax.Context
open T {SD}

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
  rename f (`  x) = ` f x
  rename f (A ∋ t)  = A ∋ rename f t
  rename f (⇉ t by eq) = ⇉ (rename f t) by eq
  rename f (op t) = op (renameMap _ f t)

  renameMap : ∀ D
    → Ren Γ Δ 
    → (⟦ D ⟧ Tm) m A Γ → (⟦ D ⟧ Tm) m A Δ
  renameMap (D ∷ _)  f (inl t) = inl (renameMapᶜ D f t)
  renameMap (_ ∷ Ds) f (inr t) = inr (renameMap Ds f t)

  renameMapᶜ : (D : ConD)
    → Ren Γ Δ
    → (⟦ D ⟧ᶜ Tm) m A Γ → (⟦ D ⟧ᶜ Tm) m A Δ
  renameMapᶜ (ι Ξ m A D) f (p , σ , q , ts) = p , σ , q , renameMapᵃˢ D f ts

  renameMapᵃˢ : (D : ArgsD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  renameMapᵃˢ ι        f _        = _
  renameMapᵃˢ (ρ D Ds) f (t , ts) = renameMapᵃ D f t , renameMapᵃˢ Ds f ts

  renameMapᵃ : (D : ArgD Ξ)
    → Ren Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  renameMapᵃ (ι m B)   f t = rename f t
  renameMapᵃ (A ∙ Δ) f t = renameMapᵃ Δ (ext f) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟨ f ⟩ t = rename f t

Sub : (Γ Δ : Ctx T) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm Infer A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts f zero    = ` zero
exts f (suc x) = rename suc (f x)

mutual
  subst : Sub Γ Δ
    → ∀ {A} → Tm m A Γ → Tm m A Δ
  subst f (` x)       = f x
  subst f (A ∋ t)     = A ∋ subst f t
  subst f (⇉ t by eq) = ⇉ (subst f t) by eq
  subst f (op t)      = op (substMap _ f t)

  substMap : ∀ D
    → Sub Γ Δ 
    → (⟦ D ⟧ Tm) m A Γ → (⟦ D ⟧ Tm) m A Δ
  substMap (D ∷ Ds) f (inl x) = inl (substMapᶜ D f x)
  substMap (D ∷ Ds) f (inr y) = inr (substMap Ds f y)

  substMapᶜ : (D : ConD)
    → Sub Γ Δ
    → (⟦ D ⟧ᶜ Tm) m A Γ → (⟦ D ⟧ᶜ Tm) m A Δ
  substMapᶜ (ι Ξ m A D) f (p , σ , q , ts) = p , σ , q , substMapᵃˢ D f ts

  substMapᵃˢ : (D : ArgsD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃˢ Tm) σ Γ → (⟦ D ⟧ᵃˢ Tm) σ Δ
  substMapᵃˢ ι        f _        = _
  substMapᵃˢ (ρ D Ds) f (t , ts) = substMapᵃ D f t , substMapᵃˢ Ds f ts

  substMapᵃ : (D : ArgD Ξ)
    → Sub Γ Δ
    → (⟦ D ⟧ᵃ Tm) σ Γ → (⟦ D ⟧ᵃ Tm) σ Δ
  substMapᵃ (ι m B) f t = subst f t
  substMapᵃ (A ∙ Δ) f t = substMapᵃ Δ (exts f) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm m A Γ → Tm m A Δ
⟪ f ⟫ t = subst f t

module _ {X : Fam ℓ} (α : (D -Alg) X) where mutual
  fold : Tm m ⇒ X m
  fold (` x)         = α .var x -- α .var x
  fold (A ∋ t)       = α .toInfer (fold t)
  fold (⇉ t by refl) = α .toCheck (fold t)
  fold (op t)        = α .alg (foldMap _ t)

  foldMap : ∀ D
    → (⟦ D ⟧ Tm) m ⇒ (⟦ D ⟧ X) m
  foldMap (D ∷ Ds) (inl t) = inl (foldMapᶜ D t)
  foldMap (D ∷ Ds) (inr t) = inr (foldMap Ds t)

  foldMapᶜ : ∀ (D : ConD)
    → (⟦ D ⟧ᶜ Tm) m ⇒ (⟦ D ⟧ᶜ X) m
  foldMapᶜ (ι Ξ m A D) (p , σ , q , ts)= p , σ , q , foldMapᵃˢ D ts

  foldMapᵃˢ : ∀ (D : ArgsD Ξ)
    → (⟦ D ⟧ᵃˢ Tm) σ ⇒₁ (⟦ D ⟧ᵃˢ X) σ
  foldMapᵃˢ ι        _        = _
  foldMapᵃˢ (ρ D Ds) (t , ts) = foldMapᵃ D t , foldMapᵃˢ Ds ts

  foldMapᵃ : ∀ (D : ArgD Ξ)
    → (⟦ D ⟧ᵃ Tm) σ ⇒₁ (⟦ D ⟧ᵃ X) σ
  foldMapᵃ (ι m B) t = fold t
  foldMapᵃ (A ∙ Δ) t = foldMapᵃ Δ t