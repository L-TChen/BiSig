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
  xs    : List (Fin Ξ)
  D     : ArgD Ξ
  Ds    : ArgsD Ξ

module _ (Ξ : ℕ) where
  data Synthesisᵃ (xs : List (Fin Ξ)) : ArgD Ξ → Set where
    nil⇉
      : (B : TExp Ξ)
      → Synthesisᵃ xs (ι Infer B)
    nil⇇
      : (B : TExp Ξ)
      → (B⊆xs : fv B ⊆ xs)
      → Synthesisᵃ xs (ι Check B)
    cons
      : (A : TExp Ξ) (D : ArgD Ξ)
      → (A⊆xs : fv A ⊆ xs) (SynD : Synthesisᵃ xs D)
      → Synthesisᵃ xs (A ∙ D)

  data Synthesisᵃˢ : List (Fin Ξ) → ArgsD Ξ → Set where
    nil
      : Synthesisᵃˢ ∅ ∅
    cons⇉
      : (D : ArgD Ξ) (Ds : ArgsD Ξ)
      → (ID : Synthesisᵃ xs D) (eq : modeArgD D ≡ Infer) (IDs : Synthesisᵃˢ xs Ds) 
      → Synthesisᵃˢ (fvArgD D ++ xs) (D ∙ Ds)
    cons⇇
      : (D : ArgD Ξ) (Ds : ArgsD Ξ)
      → (ID : Synthesisᵃ xs D) (eq : modeArgD D ≡ Check) (fvD⊆xs : fvArgD D ⊆ xs) (IDs : Synthesisᵃˢ xs Ds) 
      → Synthesisᵃˢ xs (D ∙ Ds)

Synthesis : (Ξ : ℕ) (C : TExp Ξ) (Ds : ArgsD Ξ) → Set
Synthesis Ξ C Ds = ∃[ xs ] (fv C ⊆ xs × Synthesisᵃˢ Ξ xs Ds)

ModeCorrect : ConD → Set
ModeCorrect (ι Ξ Infer C Ds) = Synthesis Ξ C Ds
ModeCorrect (ι Ξ Check C Ds) = ⊤

module _ {D : Desc} {inf : All ModeCorrect D}  where mutual
  open import Syntax.BiTyped.Raw.Term          {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
  open import Syntax.BiTyped.Extrinsic.Term    {SD} Id D

  private variable
    A B   : T
    Γ Δ   : Context T
    σ₁ σ₂ : Sub₀ Ξ
    t     : Raw⇉
    ts    : R.⟦ Ds ⟧ᵃˢ Raw

  uniq-⇉
    : (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)   = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t)  (⊢⦂ ⊢u)  = refl
  uniq-⇉ (⊢op D@(ι Ξ Infer C Ds , i , ts) (σ₁ , refl , ⊢ts)) (⊢op _ (σ₂ , refl , ⊢us)) =
    let (xs , fvC⊆xs , IDs) = A.lookup inf i in
    ≡-fv C λ x → uniq-⇉Map IDs ⊢ts ⊢us (fvC⊆xs x)

  uniq-⇉Map : Synthesisᵃˢ Ξ xs Ds
    → (⊢ts : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ Ds ⟧ᵃˢ ⊢⇄) σ₂ Γ ts)
    → ∀ {x} → x ∈ xs
    → lookup σ₁ x ≡ lookup σ₂ x
  uniq-⇉Map  nil                    _          _          ()
  uniq-⇉Map  (cons⇉ D Ds ID eq IDs) (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fvArgD D) i
  ... | inl j = uniq-⇉Mapᵃ ID eq (uniq-⇉Map IDs ⊢ts ⊢us) ⊢t ⊢u j
  ... | inr j = uniq-⇉Map  IDs ⊢ts ⊢us j
  uniq-⇉Map (cons⇇ D Ds ID _ fvD⊆xs IDs) (_ , ⊢ts) (_ , ⊢us) = uniq-⇉Map IDs ⊢ts ⊢us

  uniq-⇉Mapᵃ : {D : ArgD Ξ}
    → Synthesisᵃ Ξ xs D
    → modeArgD D ≡ Infer 
    → ({x : Fin Ξ} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → {t : R.⟦ D ⟧ᵃ Raw}
    → (⊢t : (⟦ D ⟧ᵃ ⊢⇄) σ₁ Γ t)
    → (⊢u : (⟦ D ⟧ᵃ ⊢⇄) σ₂ Γ t)
    → ∀ {x} → x ∈ fvArgD D
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ (nil⇉ B)             _ _ ⊢t ⊢u = ≡-fv-inv B (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ (cons A D A⊆xs synD) p f ⊢t ⊢u =
    let A₁=A₂ = ≡-fv A λ x∈fvA → f (A⊆xs x∈fvA) in 
    uniq-⇉Mapᵃ synD p f (subst (λ A → (⟦ D ⟧ᵃ ⊢⇄) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u