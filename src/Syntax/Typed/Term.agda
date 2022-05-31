open import Prelude

import Syntax.Typed.Signature as S

module Syntax.Typed.Term {T : Set} {O : Set} (s : S.Sig T O) where

open import Syntax.Typed.Context T
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
  → Ren (A ∙ Γ) (A ∙ Δ)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

mutual
  rename :  Ren Γ Δ → Tm A Γ     → Tm A Δ
  rename ρ (` x)                = ` ρ x
  rename ρ (op (o , refl , ts)) = op (o , refl , renameMap (arity o) ρ ts)

  renameMap : (as : Args)
    → Ren Γ Δ
    → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  renameMap ∅        ρ _        = _
  renameMap (a ∙ as) ρ (t , ts) = renameMapᵇ a ρ t , renameMap as ρ ts

  renameMapᵇ : (a : Arg)
    → Ren Γ Δ
    → (⟦ a ⟧ᵇ Tm) Γ → (⟦ a ⟧ᵇ Tm) Δ
  renameMapᵇ (∅       , A) ρ t = rename ρ t
  renameMapᵇ ((B ∙ Δ) , A) ρ t = renameMapᵇ (Δ , A) (ext ρ) t

infixr 5 ⟨_⟩_
⟨_⟩_ : Ren Γ Δ
  → ∀ {A} → Tm A Γ → Tm A Δ
⟨ ρ ⟩ t = rename ρ t

Sub : (Γ Δ : Ctx) → Set
Sub Γ Δ = ∀ {A} (x : A ∈ Γ) → Tm A Δ

exts : Sub Γ Δ → Sub (A ∙ Γ) (A ∙ Δ)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

mutual
  subst : Sub Γ Δ
    → ∀ {A} → Tm A Γ → Tm A Δ
  subst σ (` x)  = σ x
  subst σ (op (o , refl , ts)) = op (o , (refl , (substMap _ σ ts)))

  substMap : ∀ as → Sub Γ Δ → (⟦ as ⟧ᵃ Tm) Γ → (⟦ as ⟧ᵃ Tm) Δ
  substMap ∅        σ _        = _
  substMap (a ∙ as) σ (t , ts) = substMapᵇ a σ t , substMap as σ ts

  substMapᵇ : ∀ a → Sub Γ Δ → (⟦ a ⟧ᵇ Tm) Γ → (⟦ a ⟧ᵇ Tm) Δ
  substMapᵇ (∅       , A) σ t = subst σ t
  substMapᵇ ((B ∙ Δ) , A) σ t = substMapᵇ (Δ , A) (exts σ) t

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
  foldMap (a ∙ as) (t , ts) = foldMapᵇ a t , foldMap as ts

  foldMapᵇ : ∀ a → ⟦ a ⟧ᵇ Tm ⇒₁ ⟦ a ⟧ᵇ X
  foldMapᵇ (∅       , B) t = fold t
  foldMapᵇ ((A ∙ Δ) , B) t = foldMapᵇ (Δ , B) t