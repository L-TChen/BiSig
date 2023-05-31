{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Functor (SD : S.Desc) (Id : Set) where

open import Syntax.Simple SD
open B SD

private variable
  Ξ Θ : ℕ
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Mode → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (Δ : TExps Ξ) → Set ℓ → Set ℓ
⟦ []    ⟧ᵃ X = X
⟦ A ∷ Δ ⟧ᵃ X = Id × ⟦ Δ ⟧ᵃ X

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : Fam ℓ) → Set ℓ
⟦ []              ⟧ᵃˢ _ = ⊤
⟦ Δ ⊢[ d ] _ ∷ Ds ⟧ᵃˢ X = ⟦ Δ ⟧ᵃ (X d) × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ) → Fam ℓ
⟦ ι d₁  _ D ⟧ᶜ X d₂ = d₁ ≡ d₂ × ⟦ D ⟧ᵃˢ X

⟦_⟧ : (D : Desc) (X : Fam ℓ) → Fam ℓ
⟦ D ⟧ X d = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X d
