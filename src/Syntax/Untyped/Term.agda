open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Term {O : Set} (s : Sig O) where

private
  variable
    Γ Δ Ξ : Ctx

infix 40 `_

data Tm : Fam lzero where
  `_ : Fin      ⇒₁ Tm
  op : ⟦ s ⟧ Tm ⇒₁ Tm

Ren : (Γ Δ : Ctx) → Set
Ren Γ Δ = Fin Γ → Fin Δ

ext : Ren Γ Δ
  → Ren (suc Γ) (suc Δ)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

mutual
  rename : Ren Γ Δ
    → Tm Γ → Tm Δ
  rename ρ (` x)         = ` ρ x
  rename ρ (op (o , ts)) = op (o , renameMap (arity s o) ρ ts)

  renameMap : ∀ as → Ren Γ Δ
    → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  renameMap []       ρ _       = _
  renameMap (a ∷ as) ρ (t , ts) = renameMapᵇ a ρ t , renameMap as ρ ts

  renameMapᵇ : ∀ a → Ren Γ Δ
    → (⟦ a ⟧ᵇ Tm) Γ → (⟦ a ⟧ᵇ Tm) Δ
  renameMapᵇ zero    ρ t = rename ρ t
  renameMapᵇ (suc a) ρ t = renameMapᵇ a (ext ρ) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ → Tm Γ → Tm Δ
⟨ ρ ⟩ t = rename ρ t

Sub : (Γ Δ : ℕ) → Set
Sub Γ Δ = Fin Γ → Tm Δ

exts : Sub Γ Δ
  → Sub (suc Γ) (suc Δ)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

mutual
  subst : Sub Γ Δ → Tm Γ → Tm Δ
  subst σ (` x)         = σ x
  subst σ (op (f , ts)) = op (f , substMap (arity s f) σ ts)

  substMap : ∀ as → Sub Γ Δ → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  substMap []       σ _       = _
  substMap (a ∷ as) σ (t , u) = substMapᵇ a σ t , substMap as σ u

  substMapᵇ : ∀ a → Sub Γ Δ → (⟦ a ⟧ᵇ Tm) Γ → (⟦ a ⟧ᵇ Tm) Δ
  substMapᵇ zero    σ t = subst σ t
  substMapᵇ (suc a) σ t = substMapᵇ a (exts σ) t

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → Tm Γ → Tm Δ
⟪ σ ⟫ t = subst σ t

module _ {T : Fam ℓ} (α : (s -Alg) T) where mutual
  fold : Tm ⇒₁ T
  fold (` x)         = α .var x
  fold (op (o , as)) = α .alg (o , foldMap _ as)

  foldMap : ∀ as → ⟦ as ⟧ᵃ Tm ⇒₁ ⟦ as ⟧ᵃ T
  foldMap []       _       = _
  foldMap (a ∷ as) (t , u) = foldMapᵇ a t , foldMap as u

  foldMapᵇ : ∀ a → ⟦ a ⟧ᵇ Tm ⇒₁ ⟦ a ⟧ᵇ T
  foldMapᵇ zero    t = fold t
  foldMapᵇ (suc a) t = foldMapᵇ a t