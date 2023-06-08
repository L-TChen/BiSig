open import Prelude

import Syntax.Simple.Description          as S
import Syntax.BiTyped.Description         as B
import Theory.ModeCorrectness.Description as MC

module Theory.ModeCorrectness.UniqueSynthesised {SD : S.Desc}
  (Id : Set) (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

open MC SD
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
  xs    : Fins Ξ
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
  uniq-↑ᶜ (ι Syn A Ds) refl (SDs , C⊆xs) ⊢ts ⊢us =
    ≡-fv A λ x → uniq-↑ⁿ Ds SDs ⊢ts ⊢us (C⊆xs (∈ᵥ→∈fv x))

  uniq-↑ⁿ
    : (Ds : ArgsD Ξ) → Syn.ModeCorrectᵃˢ Ds
    → {ts : R.⟦ Ds ⟧ᵃˢ (Raw Θ)}
    → (⊢ts : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₁ Γ ts)
    → (⊢us : ⟦ Ds ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ₂ Γ ts)
    → ∀ {x} → x ∈ (known Ds)
    → ρ₁ x ≡ ρ₂ x -- V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ⁿ []                  _         _         _         ()
  uniq-↑ⁿ (_ ⊢[ Chk ] _ ∷ Ds) (_ , SDs) (_ , ⊢ts) (_ , ⊢us) =
    uniq-↑ⁿ Ds SDs ⊢ts ⊢us
  uniq-↑ⁿ (Δ ⊢[ Syn ] A ∷ Ds) (SD , SDs) (⊢t , ⊢ts) (⊢u , ⊢us) x∈ with L.++⁻ (fv A) x∈
  ... | inl x∈A  = uniq-↑ᵃ A Δ SD ⊢t ⊢u (uniq-↑ⁿ Ds SDs ⊢ts ⊢us) x∈A
  ... | inr x∈Ds = uniq-↑ⁿ Ds SDs ⊢ts ⊢us x∈Ds

  uniq-↑ᵃ
    : (C : TExp Ξ) (Δ : TExps Ξ) → Cover xs Δ
    → {t : R.⟦ Δ ⟧ᵃ (Raw Θ Syn)}
    → (⊢t : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Syn (C ⟨ ρ₁ ⟩)) ρ₁ Γ t)
    → (⊢u : ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ Syn (C ⟨ ρ₂ ⟩)) ρ₂ Γ t)
    → (∀ {x} → x ∈ xs → ρ₁ x ≡ ρ₂ x) -- V.lookup ρ₁ x ≡ V.lookup ρ₂ x)
    → ∀ {x} → x ∈ fv C
    → ρ₁ x ≡ ρ₂ x -- V.lookup ρ₁ x ≡ V.lookup ρ₂ x
  uniq-↑ᵃ C []      _  ⊢t ⊢u f x = ≡-fv-inv C (uniq-↑ ⊢t ⊢u) (∈fv→∈ᵥ x)
  uniq-↑ᵃ C (A ∷ Δ) SD ⊢t ⊢u f = 
    uniq-↑ᵃ C Δ (SD ∘ L.++⁺ʳ (fv A)) (subst (λ A → (⟦ Δ ⟧ᵃ _ _) _ (_ ⦂ A , _) _) A₁=A₂ ⊢t) ⊢u f
    where A₁=A₂ = ≡-fv A λ x∈ → f (SD (L.++⁺ˡ (∈ᵥ→∈fv x∈))) -- (A⊆xs (∈ᵥ→∈fv x∈))

¬switch
  : {t : Raw⇒ Θ}
  → Γ ⊢ t ⇒ A
  → B ≢ A
  → ¬ Γ ⊢ t ↑ ⇐ B
¬switch ⊢t B≠A (⊢↑ B=A ⊢t′) rewrite uniq-↑ ⊢t ⊢t′ = B≠A B=A
