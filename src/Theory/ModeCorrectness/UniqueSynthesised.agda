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
    uniq-↑ᶜ (Desc.rules D i) eq (mc i) ⊢ts ⊢us

  uniq-↑ᶜ
    : (D@(ι d A Ds) : ConD) → d ≡ Syn → ModeCorrectᶜ D
    → ∀ {ts ρ₁ ρ₂}
    → ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₁ Γ ts
    → ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₂ Γ ts
    → A ⟨ ρ₁ ⟩ ≡ A ⟨ ρ₂ ⟩
  uniq-↑ᶜ (ι Syn A Ds) refl (C⊆xs , SDs) ⊢ts ⊢us =
    ≡-fv A λ x → uniq-↑ⁿ Ds SDs ⊢ts ⊢us (C⊆xs x)

  uniq-↑ⁿ
    : (Ds : ArgsD Ξ) → Syn.ModeCorrectᵃˢ Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw Θ)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₂ Γ ts)
    → ∀ {x} → L.Any (x ∈ᵥ_) (Syn.known Ds)
    → V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ⁿ []                  _         _         _         ()
  uniq-↑ⁿ (_ ⊢[ Chk ] _ ∷ Ds) (_ , SDs) (_ , ⊢ts) (_ , ⊢us) =
    uniq-↑ⁿ Ds SDs ⊢ts ⊢us
  uniq-↑ⁿ (Δ B.⊢[ Syn ] C ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) (here px) =
    uniq-↑ᵃ C Δ SD ⊢t ⊢u (uniq-↑ⁿ Ds SDs ⊢ts ⊢us) px
  uniq-↑ⁿ (Δ B.⊢[ Syn ] C ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) (there i) =
    uniq-↑ⁿ Ds SDs ⊢ts ⊢us i

  uniq-↑ᵃ
    : (C : TExp Ξ) (Δ : TExps Ξ) → Cover As Δ
    → {t : R.⟦ Δ ⟧ᵃ (Raw Θ Syn)}
    → (⊢t : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Syn (C ⟨ ρ₁ ⟩)) ρ₁ Γ t)
    → (⊢u : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Syn (C ⟨ ρ₂ ⟩)) ρ₂ Γ t)
    → (∀ {x} → L.Any (x ∈ᵥ_) As → V.lookup ρ₁ x ≡ V.lookup ρ₂ x)
    → ∀ {x} → x ∈ᵥ C
    → V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ᵃ C []      _           ⊢t ⊢u f = ≡-fv-inv C (uniq-↑ ⊢t ⊢u)
  uniq-↑ᵃ C (A ∷ Δ) (A⊆xs ∷ SD) ⊢t ⊢u f = 
    uniq-↑ᵃ C Δ SD (subst (λ A → (⟦ Δ ⟧ᵃ _ _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f
    where A₁=A₂ = ≡-fv A λ x∈fvA → f (A⊆xs x∈fvA) 

¬switch
  : {t : Raw⇒ Θ}
  → Γ ⊢ t ⇒ A
  → B ≢ A
  → ¬ Γ ⊢ t ↑ ⇐ B
¬switch ⊢t B≠A (⊢↑ B=A ⊢t′) rewrite uniq-↑ ⊢t ⊢t′ = B≠A B=A
