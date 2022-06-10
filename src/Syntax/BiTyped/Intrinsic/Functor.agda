open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Intrinsic.Functor {SD : S.Desc} where

open import Syntax.BiTyped.Description {SD}

open import Syntax.Context
open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Mode → T → Ctx T → Set ℓ

Fam₀ = Fam lzero

private variable
  Ξ   : ℕ
  m   : Mode
  X Y : Fam ℓ
  Γ   : Ctx T
  A   : T

⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ι m B ⟧ᵃ X) σ Γ = X m (⟪ σ ⟫ B) Γ
(⟦ A ∙ D ⟧ᵃ X) σ Γ = (⟦ D ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ι      ⟧ᵃˢ _) σ _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) σ Γ = (⟦ D ⟧ᵃ X) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ m₀ B D ⟧ᶜ X) m A Γ = m₀ ≡ m × Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ Ds ⟧ X) m A Γ = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X) m A Γ

record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
  field
    var     : _∈_     ⇒ X Infer
    toInfer : X Check ⇒ X Infer
    toCheck : X Infer ⇒ X Check
    alg : (⟦ D ⟧ X) m ⇒ X m
open _-Alg public