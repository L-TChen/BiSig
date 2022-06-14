open import Prelude

import Syntax.Simple.Description  as S

module Syntax.BiTyped.Extrinsic.Properties {SD : S.Desc} (Id : Set)  where

open import Syntax.NamedContext Id
open import Syntax.Simple.Term  SD
  renaming (Tm to TExp; Tm₀ to T)
open import Syntax.Simple.Properties         {SD}

open import Syntax.BiTyped.Description       {SD}
import Syntax.BiTyped.Raw.Functor            {SD} Id as R

import      Data.List.Relation.Unary.All as A
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Vec                     as V
  using (lookup)

private variable
  Ξ     : ℕ
  A B   : T
  xs    : List (Fin Ξ)
  Γ Δ   : Context T
  D     : ArgD Ξ
  Ds    : ArgsD Ξ
  σ σ₁ σ₂ : Sub₀ Ξ
  m   : Mode

Inferᵃ : List (Fin Ξ) → ArgD Ξ → Set
Inferᵃ xs (ι Check B) = fv B ⊆ xs
Inferᵃ xs (ι Infer B) = ⊤
Inferᵃ xs (A ∙ Ds)    = fv A ⊆ xs × Inferᵃ xs Ds

data Inferᵃˢ (Ξ : ℕ) : List (Fin Ξ) → ArgsD Ξ → Set where
  ∅ 
    : Inferᵃˢ Ξ ∅ ∅
  snoc⇉
    : (ID : Inferᵃˢ Ξ xs Ds) (IDs : Inferᵃ xs D)
    → Inferᵃˢ Ξ (fvArgD D ++ xs) (D ∙ Ds)
  snoc⇇
    : (ID : Inferᵃ xs D) (IDs : Inferᵃˢ Ξ xs Ds) (fvD⊆xs : fvArgD D ⊆ xs)
    → Inferᵃˢ Ξ xs (D ∙ Ds)

Inference : (Ξ : ℕ) (C : TExp Ξ) (Ds : ArgsD Ξ) → Set
Inference Ξ C Ds = ∃[ xs ] (fv C ⊆ xs × Inferᵃˢ Ξ xs Ds)

Inferᶜ : ConD → Set
Inferᶜ (ι Ξ Infer C Ds) = Inference Ξ C Ds
Inferᶜ (ι Ξ Check C Ds) = ⊤

x∉∅ : {A : Set ℓ} {x : A}
  → x ∈ ∅ → ⊥ {lzero}
x∉∅ ()
module _ {D : Desc} (inf : All Inferᶜ D) where mutual
  open import Syntax.BiTyped.Raw.Term          {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Term  {SD}   Id D

  uniq-⇉ : {t : Raw⇉}
    → (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)   = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t)  (⊢⦂ ⊢u)  = refl
  uniq-⇉ (⊢op D@(ι Ξ Infer C Ds , i , ts) (σ₁ , refl , ⊢ts)) (⊢op _ (σ₂ , refl , ⊢us)) =
    ≡-fv σ₁ σ₂ C (uniq-⇉Map C (A.lookup inf i) ⊢ts ⊢us)

  uniq-⇉Map : (C : TExp Ξ)
    → Inference Ξ C Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → (⊢ts : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₂ Γ ts)
    → ∀ {x} → x ∈ fv C
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Map C (.∅ , C⊆xs , ∅) ⊢ts ⊢us i = ⊥-elim (x∉∅ (C⊆xs i))
  uniq-⇉Map C (.(fvArgD D ++ xs) , fvC⊆xs , snoc⇉ {xs} {_} {D} infDs IDs) (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fvArgD D) (fvC⊆xs i)
  ... | inl x∈fvD = {!   !}
  ... | inr x∈xs  = {!   !}
  uniq-⇉Map C (xs , C⊆xs , snoc⇇ ID infDs fvD⊆xs) ⊢ts ⊢us = {!   !}

  σ₁=σ₂ : ∀ AD → Inferᵃ xs AD
    → ∀ {x} → x ∈ xs
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  σ₁=σ₂ (ι Infer B) _   i = {!   !}
  σ₁=σ₂ (ι Check B) inf i = {!   !}
  σ₁=σ₂ (A ∙ AD) inf i = {!   !}

  uniq-⇉Mapᵃ : ∀ AD 
    → Inferᵃ xs AD
    → {t : R.⟦ AD ⟧ᵃ Raw}
    → (⊢t : (⟦ AD ⟧ᵃ ⊢⇄) σ₁ Γ t)
    → (⊢u : (⟦ AD ⟧ᵃ ⊢⇄) σ₂ Γ t)
    → ∀ {x} → x ∈ fvArgD AD
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ (ι Infer B) _                ⊢t ⊢u   = ≡-fv-inv _ _ B (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ (ι Check B) fvB⊆xs           ⊢t ⊢u x = {!   !}
  uniq-⇉Mapᵃ (A ∙ Ds)    (fvA⊆xs , infDs) ⊢t ⊢u x = {!   !}
    where
      helper : ∀ {x} → x ∈ fv A
        → V.lookup σ₁ x ≡ V.lookup σ₂ x
      helper x∈fvA = {! fvA⊆xs x∈fvA  !}