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
import Theory.ModeCorrectness.Functor        SD Id as M

open MC SD
open B SD
open ≡-Reasoning

private variable
  d   : Mode
  Ξ Θ : ℕ
  xs ys : Fins# Ξ
  Γ   : Cxt
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

------------------------------------------------------------------------
-- Typing derivations with substitution
-- to derivatios with partial substitution

module _ {σ : TSub Ξ 0} where
  ⊢ᵃ→Sub⊆⊢ᵃ
    : ∀ Δ {Γ} A {t}
    → {Δ⊆ : Cover (enumerate Ξ) Δ}
    → ⟦ Δ ⟧ᵃ Raw (⊢⇔ d (A ⟨ σ ⟩)) σ Γ t
    → M.⟦ Δ ⟧ᵃ (_ , Sub⇒Sub⊆ σ) Δ⊆ Raw (⊢⇔ d (sub⊆ (Sub⇒Sub⊆ σ) A λ {x} _ → ⊆enum x)) Γ t
  ⊢ᵃ→Sub⊆⊢ᵃ []      {Γ} B ⊢t rewrite sub⊆=sub σ B = ⊢t
  ⊢ᵃ→Sub⊆⊢ᵃ (A ∷ Δ) {Γ} B {x , t} {A⊆ ∷ Δ⊆} ⊢t
    rewrite sub⊆=sub σ A rewrite sub⊆-⊆-irrelevant (Sub⇒Sub⊆ σ) A  (λ {x = x₁} _ → ⊆enum x₁) A⊆ =  
    ⊢ᵃ→Sub⊆⊢ᵃ Δ B ⊢t

  ⊢ᵃˢ→Sub⊆⊢ᵃˢ
    : {Ds : ArgsD Ξ} 
    → {mc : ModeCorrectᵃˢ ys Ds}
    → {Γ  : Cxt} {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → ⟦ Ds ⟧ᵃˢ Raw ⊢⇔ σ Γ ts
    → M.⟦ Ds ⟧ᵃˢ (_ , Sub⇒Sub⊆ σ) ys (λ {x} _ → ⊆enum x) mc Raw ⊢⇔ Γ ts
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = []}                                  _          = tt
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = Δ B.⊢[ Chk ] Aₙ ∷ Ds} {A⊆ ∷ Δ⊆ , mc} {ts = t , ts} (⊢t , ⊢ts) =
     ⊢ᵃ→Sub⊆⊢ᵃ Δ Aₙ ⊢t  , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts
  ⊢ᵃˢ→Sub⊆⊢ᵃˢ {Ds = Δ ⊢[ Syn ] Aₙ ∷ Ds}   {Δ⊆ , mc}      (⊢t , ⊢ts) =
    ⊢ᵃ→Sub⊆⊢ᵃ Δ Aₙ ⊢t , ⊢ᵃˢ→Sub⊆⊢ᵃˢ ⊢ts
------------------------------------------------------------------------
-- Typing derivations with partial substitution
-- to derivatios with substitution

module _ {ρ : Sub⊆ Ξ xs} where
  Sub⊆⊢ᵃ→⊢ᵃ
    : ∀ Δ {Γ} A {t}
    → (Δ⊆ : Cover xs Δ)
    → (A⊆ : vars A #⊆ xs)
    → (⊆xs : ∀ x → x #∈ xs)
    → M.⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆ Raw (⊢⇔ d (sub⊆ ρ A A⊆)) Γ t
    → ⟦ Δ ⟧ᵃ Raw (⊢⇔ d (sub (ρ ∘ ⊆xs) A)) (ρ ∘ ⊆xs) Γ t
  Sub⊆⊢ᵃ→⊢ᵃ []      B _         B⊆ ⊆xs ⊢t rewrite sub⊆=sub′ ρ ⊆xs B B⊆ = ⊢t
  Sub⊆⊢ᵃ→⊢ᵃ (A ∷ Δ) B (A⊆ ∷ Δ⊆) B⊆ ⊆xs ⊢t rewrite sub⊆=sub′ ρ ⊆xs A A⊆ =
    Sub⊆⊢ᵃ→⊢ᵃ Δ B Δ⊆ B⊆ ⊆xs ⊢t

  Sub⊆⊢ᵃˢ→⊢ᵃˢ
    : {Ds : ArgsD Ξ} {ys : Fins# Ξ}
    → {⊆xs : (x : Fin Ξ) → x #∈ xs} {ys∪Ds⊆ : ys ∪ known Ds #⊆ xs} {mc : ModeCorrectᵃˢ ys Ds}
    → {Γ  : Cxt} {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → M.⟦ Ds ⟧ᵃˢ (_ , ρ) ys ys∪Ds⊆ mc Raw ⊢⇔ Γ ts
    → ⟦ Ds ⟧ᵃˢ Raw ⊢⇔ (Sub⊆⇒Sub ρ ⊆xs) Γ ts
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {[]}                              tt = tt
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {Δ ⊢[ Chk ] Aₙ ∷ Ds} {ys} {⊆xs} {ys∪Ds⊆} {A⊆ ∷ Ds⊆ , mc} {Γ} {t , ts} (⊢t , ⊢ts) =
     Sub⊆⊢ᵃ→⊢ᵃ Δ Aₙ _ _ _ ⊢t  , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts
  Sub⊆⊢ᵃˢ→⊢ᵃˢ {Δ ⊢[ Syn ] Aₙ ∷ Ds} {ys} {⊆xs} {ys∪Ds⊆} {mc} {Γ} {t , ts} (⊢t , ⊢ts) =
    Sub⊆⊢ᵃ→⊢ᵃ Δ Aₙ _ _ _ ⊢t , Sub⊆⊢ᵃˢ→⊢ᵃˢ ⊢ts
