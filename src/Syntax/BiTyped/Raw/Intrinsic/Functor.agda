{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Intrinsic.Functor (SD : S.Desc) where

open import Syntax.Simple SD
open B SD

private variable
  n Ξ : ℕ

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = ℕ → Mode → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (Δ : TExps Ξ) → Fam ℓ → Fam ℓ
⟦ Δ ⟧ᵃ X n mode = X (length Δ + n) mode

⟦_⟧ᵃˢ : (D : ArgsD Ξ) → Fam ℓ → (ℕ → Set ℓ)
⟦ []                   ⟧ᵃˢ _ _ = ⊤
⟦ (Δ ⊢[ mode ] _) ∷ Ds ⟧ᵃˢ X n = ⟦ Δ ⟧ᵃ X n mode × ⟦ Ds ⟧ᵃˢ X n

⟦_⟧ᶜ : (D : ConD) → Fam ℓ → Fam ℓ
⟦ ι mode  _ D ⟧ᶜ X n mode' = mode ≡ mode' × ⟦ D ⟧ᵃˢ X n

⟦_⟧ : (D : Desc) → Fam ℓ → Fam ℓ
⟦ D ⟧ X n mode = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X n mode
