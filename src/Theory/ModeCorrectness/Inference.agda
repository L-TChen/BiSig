{-# OPTIONS --with-K --rewriting #-}

open import Prelude
  hiding (lookup; _⟨_⟩_)

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as M

module Theory.ModeCorrectness.Inference {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y))
  (D : B.Desc SD) (mc : M.ModeCorrect SD Id D) where

open import Syntax.Context                SD
  renaming (Cxt to UCxt)
open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
  renaming (_⦂_ to infix 4 _⦂_)
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D
open import Syntax.BiTyped.Extrinsic.Properties     Id D

open import Theory.ModeCorrectness.UniqueSynthesised Id D mc

open M SD Id
open B SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  xs  : List (Fin Ξ)
  Γ   : Cxt   Θ
  ρ   : TSub Ξ Θ
  t u : Raw Θ d

Synthesisable : Cxt Θ → Raw⇒ Θ → Set
Synthesisable Γ t = ∃[ A ] Γ ⊢ t ⇒ A

Synthesisableᵃ
  : (Δ : TExps Ξ) → TSub Ξ Θ → Cxt Θ → R.⟦ Δ ⟧ᵃ (Raw⇒ Θ) → Set
Synthesisableᵃ {Ξ} {Θ} Δ ρ Γ t = Σ[ A ∈ TExp Ξ ] ⟦ Δ ⟧ᵃ (Raw Θ) (_⊢_⇒ A ⟨ ρ ⟩) ρ Γ t

Inheritable : Cxt Θ → Raw⇐ Θ → TExp Θ → Set
Inheritable = _⊢_⇐_

Inheritableᵃ
  : (Δ : TExps Ξ) → TSub Ξ Θ → TExp Ξ → Cxt Θ → R.⟦ Δ ⟧ᵃ (Raw⇐ Θ) → Set
Inheritableᵃ {Ξ} {Θ} Δ ρ A Γ t = ⟦ Δ ⟧ᵃ (Raw Θ) (_⊢_⇐ A ⟨ ρ ⟩) ρ Γ t

module Maybe-Checker where
  synthesise
    : (Γ : Cxt 0) (t : Raw⇒ 0)
    → Dec (Synthesisable Γ t)

  inherit
    : (Γ : Cxt 0) (t : Raw⇐ 0) (A : TExp 0)
    → Dec (Inheritable Γ t A)

  synthesise/inheritⁿ
    : {Ds : ArgsD Ξ} → (ρ : TSub Ξ 0) (Γ : Cxt 0) (ts : R.⟦ Ds ⟧ᵃˢ (Raw 0)) 
    → Maybe (⟦ Ds ⟧ᵃˢ (Raw 0) ⊢⇆ ρ Γ ts)

  synthesiseᵃ
    : (Δ : TExps Ξ) (ρ : TSub Ξ 0) (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇒ 0))
    → Maybe (Synthesisableᵃ Δ ρ Γ t)

  inheritᵃ
    : (Δ : TExps Ξ) (ρ : TSub Ξ 0) (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇐ 0)) 
      (A : TExp Ξ)
    → Maybe (Inheritableᵃ Δ ρ A Γ t)

  synthesise Γ (` x)   with lookup Γ x
  ... | no  x∉       = no λ where (A , ⊢` x∈) → x∉ (A , x∈)
  ... | yes (A , x∈) = yes (A , ⊢` x∈)

  synthesise Γ (t ⦂ A) with inherit Γ t A
  ... | no  ⊬t = no λ where (A , ⊢⦂ ⊢t) → ⊬t ⊢t
  ... | yes ⊢t = yes (A , ⊢⦂ ⊢t)

  -- Mode correctness will be used in the inductive cases
  synthesise Γ (op (i , eq , ts)) = {!!}

  inherit Γ (t ↑)  A with synthesise Γ t
  ... | no ⊬t = no λ where (⊢↑ refl ⊢t) → ⊬t (A , ⊢t)
  ... | yes (B , ⊢t) with A ≟ B
  ... | no ¬A=B = no (¬switch ⊢t ¬A=B)
  ... | yes A=B = yes (⊢↑ A=B ⊢t)

  inherit Γ (op (i , eq , ts)) A = {!!}

  synthesiseᵃ         = {!!}

  inheritᵃ            = {!!}

  synthesise/inheritⁿ = {!!}
