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
  → Ren (Ξ + Γ) (Ξ + Δ)
ext {Ξ = zero}  ρ x = ρ x
ext {Ξ = suc _} ρ zero    = zero
ext {Ξ = suc _} ρ (suc x) = suc (ext ρ x)

mutual
  rename : Ren Γ Δ
    → Tm Γ → Tm Δ
  rename ρ (` x)         = ` ρ x
  rename ρ (op (o , ts)) = op (o , renameMap (arity s o) ρ ts)

  renameMap : ∀ as → Ren Γ Δ
    → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  renameMap []       ρ _       = _
  renameMap (a ∷ as) ρ (t , ts) = rename (ext ρ) t , renameMap as ρ ts

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ → Tm Γ → Tm Δ
⟨ ρ ⟩ t = rename ρ t

Sub : (Γ Δ : ℕ) → Set
Sub Γ Δ = Fin Γ → Tm Δ

exts : Sub Γ Δ
  → Sub (Ξ + Γ) (Ξ + Δ)
exts {Ξ = zero}  σ x = σ x
exts {Ξ = suc _} σ zero    = ` zero
exts {Ξ = suc _} σ (suc x) = rename suc (exts σ x)

mutual
  subst : Sub Γ Δ → Tm Γ → Tm Δ
  subst σ (` x)         = σ x
  subst σ (op (f , ts)) = op (f , substMap (arity s f) σ ts)

  substMap : ∀ as → Sub Γ Δ → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  substMap []       σ _       = _
  substMap (a ∷ as) σ (t , u) = subst (exts σ) t , substMap as σ u

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
  foldMap (a ∷ as) (t , u) = fold t , foldMap as u