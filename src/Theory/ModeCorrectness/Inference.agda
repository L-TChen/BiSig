{-# OPTIONS --with-K #-}

open import Prelude
  hiding (lookup; _⟨_⟩_)

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as M

module Theory.ModeCorrectness.Inference {SD : S.Desc}
  (Id : Set) ⦃ decEqId : DecEq Id ⦄
  (D : B.Desc SD) (mc : M.ModeCorrect SD D) where

open import Syntax.NamedContext           SD Id
open import Syntax.NamedContext.Decidable    Id

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
  renaming (_⦂_ to infix 4 _⦂_)
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D

-- open import Syntax.BiTyped.Extrinsic.Properties     Id D

open import Theory.ModeCorrectness.UniqueSynthesised Id D mc

open M SD
open B SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  As  : TExps Θ
  xs  : List (Fin Ξ)
  Γ   : Cxt   Θ
  ρ   : TSub Ξ Θ
  t u : Raw Θ d

module _ where mutual
  synthesise
    : (Γ : Cxt 0) (t : Raw⇒ 0)
    → Dec (∃[ A ] Γ ⊢ t ⇒ A)

  inherit
    : (Γ : Cxt 0) (t : Raw⇐ 0) (A : TExp 0)
    → Dec (Γ ⊢ t ⇐ A)

  synthesise Γ (` x)   with lookup Γ x
  ... | no  x∉       = no λ where (A , ⊢` x∈) → x∉ (A , x∈)
  ... | yes (A , x∈) = yes (A , ⊢` x∈)

  synthesise Γ (t ⦂ A) with inherit Γ t A
  ... | no  ⊬t = no λ where (A , ⊢⦂ ⊢t) → ⊬t ⊢t
  ... | yes ⊢t = yes (A , ⊢⦂ ⊢t)

  synthesise Γ (op (i , t@(eq , ts))) with synthesiseᶜ (Desc.rules D i) (mc i) eq Γ t
  ... | no ⊬t  = no λ where (A , ⊢op _ ⊢t) → ⊬t (A , ⊢t)
  ... | yes (A , ⊢t) = yes (A , ⊢op _ ⊢t)

  inherit Γ (t ↑)  A with synthesise Γ t
  ... | no  ⊬t = no λ where (⊢↑ refl ⊢t) → ⊬t (A , ⊢t)
  ... | yes (B , ⊢t) with A ≟ B
  ... | no ¬A=B = no (¬switch ⊢t ¬A=B)
  ... | yes A=B = yes (⊢↑ A=B ⊢t)

  inherit Γ (op (i , t@(eq , ts))) A with inheritᶜ (Desc.rules D i) (mc i) eq Γ t A
  ... | no  ⊬t = no (λ where (⊢op _ ⊢t) → ⊬t ⊢t)
  ... | yes ⊢t = yes (⊢op _ ⊢t)

  synthesiseᶜ
    : (D : ConD) → ModeCorrectᶜ D → ConD.mode D ≡ Syn
    → (Γ : Cxt 0) (t : R.⟦ D ⟧ᶜ (Raw 0) Syn)
    → Dec (∃[ A ] ⟦ D ⟧ᶜ ⊢⇆ Syn A Γ t)
  synthesiseᶜ D (A⊆As , tt , SDs) refl Γ t = {!!}

  inheritᶜ
    : (D : ConD) → ModeCorrectᶜ D → ConD.mode D ≡ Chk
    → (Γ : Cxt 0) (t : R.⟦ D ⟧ᶜ (Raw 0) Chk) (A : TExp 0)
    → Dec (⟦ D ⟧ᶜ ⊢⇆ Chk A Γ t)
  inheritᶜ (ι Chk A Ds) mc refl Γ t A₀ = {!!}

  synthesise/inhertⁿ
    : (Ds : ArgsD Ξ) → ModeCorrectᵃˢ As Ds
    → (Γ : Cxt 0) (ts : R.⟦ Ds ⟧ᵃˢ (Raw 0))
    → Dec {!!}
  synthesise/inhertⁿ = {!!}

  synthesiseᵃ
    : (Δ : TExps Ξ) (ρ : TSub Ξ 0) (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇒ 0))
    → Dec {!!}

  inheritᵃ
    : (Δ : TExps Ξ) (ρ : TSub Ξ 0) (Γ : Cxt 0) (t : R.⟦ Δ ⟧ᵃ (Raw⇐ 0)) 
      (A : TExp Ξ)
    → Dec {!!}

  synthesiseᵃ         = {!!}

  inheritᵃ            = {!!}

