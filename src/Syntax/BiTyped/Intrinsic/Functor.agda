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
  B   : TExp Ξ

⟦_⟧ᵃ_ : List (TExp Ξ) → (Ctx T → Set ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ∅     ⟧ᵃ X) _ Γ = X Γ
(⟦ A ∙ D ⟧ᵃ X) σ Γ = (⟦ D ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ∅               ⟧ᵃˢ _) σ _ = ⊤
(⟦ Δ ⊢[ m ] B ∙ Ds ⟧ᵃˢ X) σ Γ = (⟦ Δ ⟧ᵃ X m (⟪ σ ⟫ B)) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι m₀ B D ⟧ᶜ X) m A Γ = m₀ ≡ m × Σ[ σ ∈ Sub₀ _ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ Ds ⟧ X) m A Γ = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X) m A Γ

record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
  field
    var     : _∈_     ⇒ X Infer
    toInfer : X Check ⇒ X Infer
    toCheck : X Infer ⇒ X Check
    alg : (⟦ D ⟧ X) m ⇒ X m
open _-Alg public