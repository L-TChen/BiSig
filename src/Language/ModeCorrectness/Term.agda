open import Prelude

import Syntax.Simple.Description as S
open import Syntax.BiTyped.Description

import Language.ModeCorrectness.Description as B

module Language.ModeCorrectness.Term {SD : S.Desc}
  (Id : Set) (_≟Id_ : (x y : Id) → Dec (x ≡ y))
  (D : Desc {SD}) (modeCorrect : B.AllModeCorrect Id D) where

open B {SD} Id

import      Data.Vec                     as V
import      Data.List.Relation.Unary.All as A
open import Data.List.Relation.Unary.Any.Properties

open import Syntax.NamedContext Id
open import Syntax.NamedContext.Decidable _≟Id_

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T; _≟_ to _≟T_)
open import Syntax.Simple.Properties         {SD}

import      Syntax.BiTyped.Raw.Functor       {SD} Id as R
open import Syntax.BiTyped.Raw.Term          {SD} Id D
open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
open import Syntax.BiTyped.Extrinsic.Term    {SD} Id D

private variable
  Ξ     : ℕ
  A B   : T
  xs    : List (Fin Ξ)
  Γ     : Context T
  ADs   : ArgsD Ξ
  AD    : ArgD Ξ
  σ₁ σ₂ : Sub₀ Ξ
  m     : Mode
  t     : Raw m
  ts    : R.⟦ ADs ⟧ᵃˢ Raw

mutual
  uniq-⇉
    : (⊢t : Γ ⊢ t ⇉ A) (⊢u : Γ ⊢ t ⇉ B)
    → A ≡ B
  uniq-⇉ (⊢` x)   (⊢` y)   = uniq-∈ x y
  uniq-⇉ (⊢⦂ ⊢t)  (⊢⦂ ⊢u)  = refl
  uniq-⇉ (⊢op (ι Infer C Ds , i , ts) (σ₁ , refl , ⊢ts)) (⊢op _ (σ₂ , refl , ⊢us)) =
    let (xs , fvC⊆xs , IDs) = A.lookup modeCorrect i in
    ≡-fv C (λ x → uniq-⇉Map IDs ⊢ts ⊢us (fvC⊆xs x))

  uniq-⇉Map : {xs : List (Fin Ξ)}
    → Synthesisᵃˢ xs ADs
    → (⊢ts : (⟦ ADs ⟧ᵃˢ Raw , ⊢⇄) σ₁ Γ ts)
    → (⊢us : (⟦ ADs ⟧ᵃˢ Raw , ⊢⇄) σ₂ Γ ts)
    → ∀ {x} → x ∈ xs
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Map nil                   _   _   ()
  uniq-⇉Map (cons⇉ Θ C Ds SD SDs) (⊢t , ⊢ts) (⊢u , ⊢us) i with ++⁻ (fv C) i
  ... | inl j = uniq-⇉Mapᵃ C Θ SD ⊢t ⊢u (uniq-⇉Map SDs ⊢ts ⊢us) j
  ... | inr j = uniq-⇉Map SDs ⊢ts ⊢us j
  uniq-⇉Map (cons⇇ _ _ _ _ _ SDs) (_ , ⊢ts)  (_ , ⊢us)  = uniq-⇉Map SDs ⊢ts ⊢us

  uniq-⇉Mapᵃ
    : (C : TExp Ξ)
    → (Θ : TExps Ξ)
    → ModeCorrectᵃ xs Θ
    → {t : R.⟦ Θ ⟧ᵃ Raw Infer}
    → (⊢t : (⟦ Θ ⟧ᵃ Raw , ⊢⇄ Infer (⟪ σ₁ ⟫ C)) σ₁ Γ t)
    → (⊢u : (⟦ Θ ⟧ᵃ Raw , ⊢⇄ Infer (⟪ σ₂ ⟫ C)) σ₂ Γ t)
    → ({x : Fin Ξ} → x ∈ xs → V.lookup σ₁ x ≡ V.lookup σ₂ x)
    → ∀ {x} → x ∈ fv C
    → V.lookup σ₁ x ≡ V.lookup σ₂ x
  uniq-⇉Mapᵃ C ∅ _                 ⊢t ⊢u f = ≡-fv-inv C (uniq-⇉ ⊢t ⊢u)
  uniq-⇉Mapᵃ C (A ∙ Θ) (A⊆xs , SD) ⊢t ⊢u f =
     let A₁=A₂ = ≡-fv A λ x∈fvA → f (A⊆xs x∈fvA) in 
     uniq-⇉Mapᵃ C Θ SD (subst (λ A → (⟦ Θ ⟧ᵃ _ , _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f

mutual
  synthesize
    : (Γ : Context T) (t : Raw⇉)
    → Dec (∃[ A ] Γ ⊢ t ⇉ A)
  synthesize Γ (` x)   with lookup Γ x
  ... | no ¬p       = no λ where (A , ⊢` x∈) → ¬p (A , x∈)
  ... | yes (A , x) = yes (A , ⊢` x)
  synthesize Γ (t ⦂ A) with inherit Γ t A
  ... | no ¬p = no λ where (B , ⊢⦂ ⊢t) → ¬p ⊢t
  ... | yes p = yes (A , ⊢⦂ p)
  synthesize Γ (op (_ , i , ts))  = {!   !}

  inherit
    : (Γ : Context T) (t : Raw⇇) (A : T)
    → Dec (Γ ⊢ t ⇇ A)
  inherit Γ (t ↑)  A with synthesize  Γ t
  ... | no ¬p = no λ where (⊢⇉ ⊢t refl) → ¬p (A , ⊢t)
  ... | yes (B , ⊢t) with B ≟T A
  ... | no ¬q = no λ where (⊢⇉ ⊢u refl) → ¬q (uniq-⇉ ⊢t ⊢u)
  ... | yes A=B = yes (⊢⇉ ⊢t A=B)
  inherit Γ (op (_ , i , ts)) A = {!   !}
