{-# OPTIONS --safe #-}

import Syntax.Simple.Description as S

module Syntax.BiTyped.Functor (SD : S.Desc) where

open import Prelude

open import Syntax.Simple              SD
open import Syntax.Context             SD
import      Syntax.Typed.Raw.Functor   SD as R
open import Syntax.BiTyped.Description SD as B
open import Theory.Erasure.Description

Fam : (ℓ′ : Level) (X : R.Fam ℓ) → Set (lmax ℓ (lsuc ℓ′))
Fam ℓ′ X = (Γ : Cxt₀) → X (length Γ) → Mode → TExp₀ → Set ℓ′

Fam₀ : (X : R.Fam ℓ) → Set (lmax ℓ (lsuc lzero))
Fam₀ = Fam lzero

private variable
  Ξ : ℕ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : (Γ : Cxt₀) → X (length Γ) → Set ℓ′)
     → TSub Ξ 0 → (Γ : Cxt₀) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set ℓ′
⟦ []    ⟧ᵃ X Y σ Γ t = Y Γ t
⟦ A ∷ Δ ⟧ᵃ X Y σ Γ t = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) t

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → TSub Ξ 0 → (Γ : Cxt₀) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X (length Γ) → Set ℓ′
⟦ []              ⟧ᵃˢ _ _ _ _ _        = ⊤
⟦ Δ ⊢[ d ] A ∷ Ds ⟧ᵃˢ X Y σ Γ (x , xs) =
  ⟦ Δ ⟧ᵃ X (λ Γ x' → Y Γ x' d (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι {Ξ} d B D ⟧ᶜ X Y Γ xs d′ A =
  d ≡ d′ × Σ[ σ ∈ TSub Ξ 0 ] B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y Γ (i , xs) d A = ⟦ D .rules i ⟧ᶜ X Y Γ xs d A
