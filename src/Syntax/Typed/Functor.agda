import Syntax.Simple.Description as S

module Syntax.Typed.Functor (SD : S.Desc) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.Context           SD
open import Syntax.Typed.Description SD
import      Syntax.Typed.Raw.Functor SD as R

Fam : (ℓ′ : Level) → (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc ℓ′)
Fam ℓ′ X = (Γ : Cxt 0) → X (length Γ) → Ty → Set ℓ′

Fam₀ : (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc 0ℓ)
Fam₀ X = Fam 0ℓ X

private variable
  Ξ : ℕ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : (Γ : Cxt 0) → X (length Γ) → Set ℓ′)
     → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set ℓ′
⟦ []    ⟧ᵃ X Y σ Γ x = Y Γ x
⟦ A ∷ Δ ⟧ᵃ X Y σ Γ x = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ D ⟧ᵃˢ X (length Γ) → Set ℓ′
⟦ []           ⟧ᵃˢ _ _ _ _ _        = ⊤
⟦ (Δ ⊢ A) ∷ Ds ⟧ᵃˢ X Y σ Γ (x , xs) =
  ⟦ Δ ⟧ᵃ X (λ Γ' x' → Y Γ' x' (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ D ⟧ᶜ X)
⟦ ι {Ξ} B D ⟧ᶜ X Y Γ xs A = Σ[ σ ∈ TSub Ξ 0 ] B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ D ⟧ X)
⟦ D ⟧ X Y Γ (i , xs) A = ⟦ D .rules i ⟧ᶜ X Y Γ xs A
