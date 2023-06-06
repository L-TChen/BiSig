{-# OPTIONS --safe #-}

import Syntax.Simple.Description as S

module Syntax.Typed.Functor (SD : S.Desc) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.Context           SD
open import Syntax.Typed.Description SD
import      Syntax.Typed.Raw.Functor SD as R

Fam : (ℓ′ : Level) → (X : R.Fam ℓ) → Set (lmax ℓ (lsuc ℓ′))
Fam ℓ′ X = (Γ : Cxt₀) → X (length Γ) → TExp₀ → Set ℓ′

Fam₀ : (X : R.Fam ℓ) → Set (lmax ℓ (lsuc lzero))
Fam₀ X = Fam lzero X

private variable
  Ξ : ℕ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : (Γ : Cxt₀) → X (length Γ) → Set ℓ′)
     → TSub Ξ 0 → (Γ : Cxt₀) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set ℓ′
⟦ []    ⟧ᵃ X Y ρ Γ x = Y Γ x
⟦ A ∷ Δ ⟧ᵃ X Y ρ Γ x = ⟦ Δ ⟧ᵃ X Y ρ ((A ⟨ ρ ⟩) ∷ Γ) x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → TSub Ξ 0 → (Γ : Cxt₀) → R.⟦ D ⟧ᵃˢ X (length Γ) → Set ℓ′
⟦ []           ⟧ᵃˢ _ _ _ _ _        = ⊤
⟦ (Δ ⊢ A) ∷ Ds ⟧ᵃˢ X Y ρ Γ (x , xs) =
  ⟦ Δ ⟧ᵃ X (λ Γ x → Y Γ x (A ⟨ ρ ⟩)) ρ Γ x × ⟦ Ds ⟧ᵃˢ X Y ρ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ D ⟧ᶜ X)
⟦ ι {Ξ} B D ⟧ᶜ X Y Γ x A = Σ[ ρ ∈ TSub Ξ 0 ] B ⟨ ρ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y ρ Γ x

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ D ⟧ X)
⟦ D ⟧ X Y Γ (i , xs) A = ⟦ D .rules i ⟧ᶜ X Y Γ xs A
