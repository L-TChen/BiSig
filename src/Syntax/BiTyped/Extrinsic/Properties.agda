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
  cons⇉
    :  (ID : Inferᵃ xs D) (IDs : Inferᵃˢ Ξ xs Ds) (m=Infer : modeArgD D ≡ Infer)
    → Inferᵃˢ Ξ (fvArgD D ++ xs) (D ∙ Ds)
  cons⇇
    : (ID : Inferᵃ xs D) (IDs : Inferᵃˢ Ξ xs Ds) (m=Check : modeArgD D ≡ Check) (fvD⊆xs : fvArgD D ⊆ xs)
    → Inferᵃˢ Ξ xs (D ∙ Ds)

Inference : (Ξ : ℕ) (C : TExp Ξ) (Ds : ArgsD Ξ) → Set
Inference Ξ C Ds = ∃[ xs ] (fv C ⊆ xs × Inferᵃˢ Ξ xs Ds)

Inferᶜ : ConD → Set
Inferᶜ (ι Ξ Infer C Ds) = Inference Ξ C Ds
Inferᶜ (ι Ξ Check C Ds) = ⊤

x∉∅ : {A : Set ℓ} {x : A}
  → x ∈ ∅ → ⊥ {lzero}
x∉∅ ()

module _ {D : Desc} {inf : All Inferᶜ D}  where mutual
  open import Syntax.BiTyped.Raw.Term          {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Term    {SD} Id D

  uniq-⇉ : {t : Raw⇉}
    → (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)   = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t)  (⊢⦂ ⊢u)  = refl
  uniq-⇉ (⊢op D@(ι Ξ Infer C Ds , i , ts) (σ₁ , refl , ⊢ts)) (⊢op _ (σ₂ , refl , ⊢us)) =
    let (xs , fvC⊆xs , IDs) = A.lookup inf i in 
    ≡-fv σ₁ σ₂ C λ x → uniq-⇉Map xs IDs ⊢ts ⊢us (fvC⊆xs x)

  uniq-⇉Map : (xs : List (Fin Ξ))
    → Inferᵃˢ Ξ xs Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ Raw}
    → (⊢ts : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₂ Γ ts)
    → ∀ {x} → x ∈ xs
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Map .∅               ∅                                    ⊢ts ⊢us i = ⊥-elim $ x∉∅ i
  uniq-⇉Map .(fvArgD D ++ _) (cons⇉ {xs} {D} {Ds} ID IDs m=Infer) (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fvArgD D) i
  ... | inl j = uniq-⇉Mapᵃ xs D ID (uniq-⇉Map xs IDs ⊢ts ⊢us) ⊢t ⊢u m=Infer i
  ... | inr j = uniq-⇉Map xs IDs ⊢ts ⊢us j
  uniq-⇉Map xs (cons⇇ ID IDs m=Check fvD⊆xs) (_ , ⊢ts) (_ , ⊢us) i  = uniq-⇉Map xs IDs ⊢ts ⊢us i

  uniq-⇉Mapᵃ : (xs : List (Fin Ξ)) (AD : ArgD Ξ) 
    → Inferᵃ xs AD
    → (∀ {x} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → {t : R.⟦ AD ⟧ᵃ Raw}
    → (⊢t : (⟦ AD ⟧ᵃ ⊢⇄) σ₁ Γ t)
    → (⊢u : (⟦ AD ⟧ᵃ ⊢⇄) σ₂ Γ t)
    → modeArgD AD ≡ Infer → ∀ {x} → x ∈ fvArgD AD ++ xs
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ xs (ι Infer B) _              f ⊢t ⊢u refl i with ++⁻ (fv B) i
  ... | inl j = ≡-fv-inv _ _ B (uniq-⇉ ⊢t ⊢u) j
  ... | inr j = f j
  uniq-⇉Mapᵃ {σ₁ = σ₁} {σ₂} {Γ} xs (A ∙ AD)    (fvA⊆xs , ID) f ⊢t ⊢u p    i with ++⁻ (fvArgD AD) i
  ... | inr j = f j
  ... | inl j = uniq-⇉Mapᵃ xs AD ID f (subst (λ A → (⟦ AD ⟧ᵃ ⊢⇄) σ₁ (_ ⦂ A , Γ) _) A₁=A₂ ⊢t) ⊢u p i -- {! uniq-⇉Mapᵃ xs AD ID f   !}
    where
      helper : ∀ {x} → x ∈ fv A → V.lookup σ₁ x ≡ V.lookup σ₂ x
      helper x∈fvA = f (fvA⊆xs  x∈fvA)

      A₁=A₂ : sub σ₁ A ≡ sub σ₂ A
      A₁=A₂ = ≡-fv σ₁ σ₂ A helper
