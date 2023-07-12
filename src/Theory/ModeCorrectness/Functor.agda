import Syntax.Simple.Signature as S

module Theory.ModeCorrectness.Functor (SD : S.SigD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Syntax.BiTyped.Signature SD
import      Syntax.Typed.Raw.Functor   SD as R
import      Syntax.BiTyped.Functor     SD as B

open import Theory.Erasure

open import Theory.ModeCorrectness.Signature SD

private variable
  Ξ : ℕ

⟦_⟧ᵃ : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) → Cover xs Δ
     → (X : R.Fam ℓ) → ((Γ : Cxt 0) → X (length Γ) → Set ℓ′)
     → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ)
     → Set ℓ′
⟦ []    ⟧ᵃ _  _                   X Y Γ t = Y Γ t
⟦ A ∷ Δ ⟧ᵃ (xs , ρ) (A⊆xs ∷ Δ⊆xs) X Y Γ t =
  ⟦ Δ ⟧ᵃ (xs , ρ) Δ⊆xs X Y (sub⊆ ρ A A⊆xs ∷ Γ) t

⟦_⟧ᵃˢ : (Ds : ArgsD Ξ) ((xs , ρ) : ∃Sub⊆ Ξ)
      → (ys : Fins# Ξ)→ ys ∪ known Ds #⊆ xs
      → (MC : ModeCorrectᵃˢ ys Ds)
      → (X : R.Fam ℓ) (Y : B.Fam ℓ′ X)
      → (Γ : Cxt 0) → R.⟦ eraseᵃˢ Ds ⟧ᵃˢ X (length Γ) → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _ _ _ _ _ _ = ⊤

⟦ Δ ⊢[ Chk ] A ∷ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs (A⊆Ds ∷ Δ⊆Ds , MC) X Y Γ (t , ts) =
    ⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆xs X (λ Γ t → Y Γ t Chk (sub⊆ ρ A (Ds⊆xs ∘ A⊆Ds))) Γ t
  × ⟦ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs MC X Y Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {A} A⊆ {x} x∈ → Ds⊆xs (A⊆ x∈)) Δ⊆Ds

⟦ Δ ⊢[ Syn ] A ∷ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs (Δ⊆Ds , MC) X Y Γ (t , ts) =
    ⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆xs X (λ Γ t → Y Γ t Syn (sub⊆ ρ A (Ds⊆xs ∘ ∪⁺ʳ ys ∘ ∪⁺ˡ))) Γ t
    × ⟦ Ds ⟧ᵃˢ (xs , ρ) ys (Ds⊆xs ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars A))) MC X Y Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {B} B⊆ {x} x∈ → Ds⊆xs (∪-monotoneʳ ys (∪⁺ʳ (vars A)) (B⊆ x∈))) Δ⊆Ds
