open import Prelude

import Syntax.Typed.Signature as S

module Syntax.Typed.Term {T : Set} {O : Set} (s : S.Sig T O) where

open import Syntax.Context T
open S   T hiding (arity; sort)
open Sig s

private
  variable
    A B   : T 
    Γ Δ Ξ : Ctx

infix 40 `_

data Tm : T → Ctx → Set where
  `_ : _∈_      ⇒ Tm
  op : ⟦ s ⟧ Tm ⇒ Tm 

Ren : (Γ Δ : Ctx) → Set
Ren Γ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

ext : Ren Γ Δ
  → Ren (Ξ ++ Γ) (Ξ ++ Δ)
ext {Ξ = ∅}     ρ x = ρ x
ext {Ξ = _ ∙ _} ρ zero    = zero
ext {Ξ = _ ∙ _} ρ (suc x) = suc (ext ρ x)

mutual
  rename :  Ren Γ Δ → Tm A Γ     → Tm A Δ
  rename ρ (` x)                = ` ρ x
  rename ρ (op (o , refl , ts)) = op (o , refl , renameMap (arity o) ρ ts)

  renameMap : (as : Args)
    → Ren Γ Δ
    → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  renameMap ∅        ρ _        = _
  renameMap (x ∙ as) ρ (t , ts) = rename (ext ρ) t , renameMap as ρ ts

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟨ ρ ⟩ t = rename ρ t

Sub : (Γ Δ : Ctx) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm A Δ

exts : Sub Γ Δ → Sub (Ξ ++ Γ) (Ξ ++ Δ)
exts {Ξ = ∅}     σ         = σ
exts {Ξ = _ ∙ _} σ zero    = ` zero
exts {Ξ = _ ∙ _} σ (suc x) = rename suc (exts σ x)

mutual
  subst : Sub Γ Δ
    → ∀ {A} → Tm A Γ → Tm A Δ
  subst σ (` x)  = σ x
  subst σ (op (o , refl , ts)) = op (o , (refl , (substMap _ σ ts)))

  substMap : ∀ as → Sub Γ Δ → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  substMap ∅        σ _        = _
  substMap (a ∙ as) σ (t , ts) = subst (exts σ) t , substMap as σ ts

infixr 5 ⟪_⟫_
⟪_⟫_ : Sub Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟪ σ ⟫ t = subst σ t

module _ {X : Fam ℓ} (α : (s -Alg) X) where mutual
  fold : Tm ⇒ X
  fold (` x)              = α .var x
  fold (op (o , eq , as)) = α .alg ((o , eq , foldMap _ as))

  foldMap : ∀ as → ⟦ as ⟧ᵃ Tm ⇒₁ ⟦ as ⟧ᵃ X
  foldMap ∅        _        = _
  foldMap (a ∙ as) (t , ts) = fold t , foldMap as ts