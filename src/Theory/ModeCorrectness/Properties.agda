{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as MC

module Theory.ModeCorrectness.Properties {SD : S.Desc}
  (Id : Set) ⦃ decEqId : DecEq Id ⦄
  (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

import Data.List.Relation.Unary.All as All

open import Syntax.NamedContext           SD Id
  hiding (Cxt)
  renaming (Cxt₀ to Cxt)
open import Syntax.NamedContext.Decidable    Id

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor            SD Id as R
open import Syntax.BiTyped.Raw.Term                  Id D
  hiding (Raw⇐; Raw⇒; Raw)
  renaming (_⦂_ to infix 4 _⦂_; Raw⇐₀ to Raw⇐; Raw⇒₀ to Raw⇒; Raw₀ to Raw)
open import Syntax.BiTyped.Extrinsic.Functor      SD Id
open import Syntax.BiTyped.Extrinsic.Term            Id D

open import Theory.ModeCorrectness.UniqueSynthesised Id D mc
open import Theory.ModeCorrectness.Functor        SD Id as M

open MC SD
open B SD
open ≡-Reasoning

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  As  : TExps Θ
  xs  : Fins Ξ
  Γ   : Cxt
  ρ   : TSub Ξ Θ
  t u : Raw d

ρ≤σ→⊢tᵃ
  : {ρ σ : ∃Sub⊆ Ξ} → ρ ≤ σ
  → (Δ : TExps Ξ) {Δ⊆xs : Cover _ Δ} {Δ⊆xs′ : Cover _ Δ}
  → {Γ : Cxt} (t : R.⟦ Δ ⟧ᵃ (Raw d)) {A : Ty}
  → M.⟦ Δ ⟧ᵃ σ Δ⊆xs  Raw (⊢⇔ d A) Γ t
  → M.⟦ Δ ⟧ᵃ ρ Δ⊆xs′ Raw (⊢⇔ d A) Γ t
ρ≤σ→⊢tᵃ = {!!}

ρ≤σ→⊢tᵃ′
  : {ρ σ : ∃Sub⊆ Ξ} → ρ ≤ σ
  → (Δ : TExps Ξ) {Δ⊆xs : Cover _ Δ} {Δ⊆xs′ : Cover _ Δ}
  → {Γ : Cxt} (t : R.⟦ Δ ⟧ᵃ (Raw d)) {A : Ty}
  → M.⟦ Δ ⟧ᵃ ρ Δ⊆xs′ Raw (⊢⇔ d A) Γ t
  → M.⟦ Δ ⟧ᵃ σ Δ⊆xs  Raw (⊢⇔ d A) Γ t
ρ≤σ→⊢tᵃ′ = {!!}

ρ≤σ→⊢tⁿ′
  : {ρ σ : ∃Sub⊆ Ξ} → ρ ≤ σ
  → (Ds : ArgsD Ξ) (ys : Fins# Ξ) (mc : ModeCorrectᵃˢ ys Ds)
  → (Ds⊆  : ys ∪ known Ds #⊆ _)
  → (Ds⊆′ : ys ∪ known Ds #⊆ _)
  → {Γ : Cxt} (ts : R.⟦ Ds ⟧ᵃˢ Raw)
  → M.⟦ Ds ⟧ᵃˢ ρ ys Ds⊆  mc Raw ⊢⇔ Γ ts 
  → M.⟦ Ds ⟧ᵃˢ σ ys Ds⊆′ mc Raw ⊢⇔ Γ ts 
ρ≤σ→⊢tⁿ′ = {!!}
