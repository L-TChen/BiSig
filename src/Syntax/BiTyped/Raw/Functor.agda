{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Functor {SD : S.Desc} (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open B {SD}

private variable
  n m : ℕ
  mod : Mode
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Mode → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (D : List (TExp n)) → Set ℓ → Set ℓ
⟦ ∅     ⟧ᵃ X = X
⟦ A ∙ Θ ⟧ᵃ X = Id × ⟦ Θ ⟧ᵃ X

⟦_⟧ᵃˢ : (D : ArgsD n) (X : Fam ℓ) → Set ℓ
⟦ ∅               ⟧ᵃˢ _ = ⊤
⟦ Θ ⊢[ m ] _ ∙ Ds ⟧ᵃˢ X = ⟦ Θ ⟧ᵃ (X m) × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ) → Fam ℓ
⟦ ι mod₁  _ D ⟧ᶜ X mod₂ = mod₁ ≡ mod₂ × ⟦ D ⟧ᵃˢ X
-- (⟦ ι _     _ D ⟧ᶜ X) _    = ⊥

⟦_⟧ : (D : Desc) (X : Fam ℓ) → Fam ℓ
⟦ Ds ⟧ X mod = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] ⟦ D ⟧ᶜ X mod
