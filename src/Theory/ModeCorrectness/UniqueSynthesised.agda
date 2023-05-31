{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description          as S
import Syntax.BiTyped.Description         as B
import Theory.ModeCorrectness.Description as M

module Theory.ModeCorrectness.UniqueSynthesised {SD : S.Desc}
  (Id : Set) (D : B.Desc SD) (mc : M.ModeCorrect SD D) where

open M SD
open B SD

open import Syntax.NamedContext           SD Id

open import Syntax.Simple SD

import      Syntax.BiTyped.Raw.Functor           SD Id as R
open import Syntax.BiTyped.Raw.Term                 Id D
  renaming (_⦂_ to infix 4 _⦂_)
open import Syntax.BiTyped.Extrinsic.Functor     SD Id
open import Syntax.BiTyped.Extrinsic.Term           Id D

private variable
  Ξ Θ : ℕ
  xs    : List (Fin Ξ)
  Γ     : Cxt  Θ
  A B   : TExp Ξ
  As    : TExps Ξ
  ρ₁ ρ₂ : TSub  Ξ Θ

------------------------------------------------------------------------------
-- Uniqueness of Synthesised Types

mutual
  uniq-↑
    : {t : Raw⇒ Θ}
    → (⊢t : Γ ⊢ t ⇒ A) (⊢u : Γ ⊢ t ⇒ B)
    → A ≡ B
  uniq-↑ (⊢` x)    (⊢` y)   = uniq-∈ x y
  uniq-↑ (⊢⦂ ⊢t )  (⊢⦂ ⊢u ) = refl
  uniq-↑ (⊢op (i , eq , _) (ts , refl , ⊢ts)) (⊢op _ (us , refl , ⊢us)) =
    uniq-↑ᶜ (Desc.rules D i) (mc i) eq ⊢ts ⊢us

  uniq-↑ᶜ
    : ∀ D → ModeCorrectᶜ D → ConD.mode D ≡ Inf
    → ∀ {ts ρ₁ ρ₂}
    → ⟦ ConD.args D ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₁ Γ ts
    → ⟦ ConD.args D ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₂ Γ ts
    → ConD.type D ⟨ ρ₁ ⟩ ≡ ConD.type D ⟨ ρ₂ ⟩
  uniq-↑ᶜ D (C⊆xs , _ , SDs) refl ⊢ts ⊢us =
    ≡-fv (ConD.type D) λ x → uniq-↑ⁿ (ConD.args D) SDs ⊢ts ⊢us (C⊆xs x)

  uniq-↑ⁿ
    : (Ds : ArgsD Ξ)
    → ModeCorrectᵃˢ [] Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw Θ)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₂ Γ ts)
    → ∀ {x} → x ∈ᵥ Known [] Ds
    → V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ⁿ []                  _             _          _         ()
  uniq-↑ⁿ (_ ⊢[ Chk ] _ ∷ Ds) (_ , _ , SDs) (_ , ⊢ts)  (_ , ⊢us) =
    uniq-↑ⁿ Ds SDs ⊢ts ⊢us
  uniq-↑ⁿ (Δ B.⊢[ Inf ] C ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) (here px) =
    uniq-↑ᵃ C Δ SD ⊢t ⊢u (uniq-↑ⁿ Ds SDs ⊢ts ⊢us) px
  uniq-↑ⁿ (Δ B.⊢[ Inf ] C ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) (there i) =
    uniq-↑ⁿ Ds SDs ⊢ts ⊢us i

  uniq-↑ᵃ
    : (C : TExp Ξ) (Δ : TExps Ξ)
    → ModeCorrectᵃ As Δ
    → {t : R.⟦ Δ ⟧ᵃ (Raw Θ Inf)}
    → (⊢t : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Inf (C ⟨ ρ₁ ⟩)) ρ₁ Γ t)
    → (⊢u : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Inf (C ⟨ ρ₂ ⟩)) ρ₂ Γ t)
    → (∀ {x} → x ∈ᵥ As → V.lookup ρ₁ x ≡ V.lookup ρ₂ x)
    → ∀ {x} → x ∈ₜ C
    → V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ᵃ C []      _           ⊢t ⊢u f = ≡-fv-inv C (uniq-↑ ⊢t ⊢u)
  uniq-↑ᵃ C (A ∷ Δ) (A⊆xs , SD) ⊢t ⊢u f = 
    uniq-↑ᵃ C Δ SD (subst (λ A → (⟦ Δ ⟧ᵃ _ _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f
    where A₁=A₂ = ≡-fv A λ x∈fvA → f (A⊆xs x∈fvA) 

¬switch
  : {t : Raw⇒ Θ}
  → Γ ⊢ t ⇒ A
  → B ≢ A
  → ¬ Γ ⊢ t ↑ ⇐ B
¬switch ⊢t B≠A (⊢↑ B=A ⊢t′) rewrite uniq-↑ ⊢t ⊢t′ = B≠A B=A
