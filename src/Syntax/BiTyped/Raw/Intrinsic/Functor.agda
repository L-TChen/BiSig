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
⟦ Δ ⟧ᵃ X n d = X (length Δ ʳ+ n) d

⟦_⟧ᵃˢ : (D : ArgsD Ξ) → Fam ℓ → (ℕ → Set ℓ)
⟦ []                ⟧ᵃˢ _ _ = ⊤
⟦ (Δ ⊢[ d ] _) ∷ Ds ⟧ᵃˢ X n = ⟦ Δ ⟧ᵃ X n d × ⟦ Ds ⟧ᵃˢ X n

⟦_⟧ᶜ : (D : ConD) → Fam ℓ → Fam ℓ
⟦ ι d  _ D ⟧ᶜ X n d' = d ≡ d' × ⟦ D ⟧ᵃˢ X n

⟦_⟧ : (D : Desc) → Fam ℓ → Fam ℓ
⟦ D ⟧ X n d = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X n d
