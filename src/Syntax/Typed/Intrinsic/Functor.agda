open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Intrinsic.Functor {SD : S.Desc}  where

open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)
open import Syntax.Context

open import Syntax.Typed.Description {SD}

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Ctx T → Set ℓ

Fam₀ = Fam lzero

private variable
  A B   : T
  Γ Δ Ξ : ℕ
  X Y   : Fam ℓ
 
⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Sub Ξ 0 → Ctx T → Set ℓ
(⟦ ⊢    B ⟧ᵃ X) σ Γ = X (⟪ σ ⟫ B) Γ
(⟦ A ∙ As ⟧ᵃ X) σ Γ = (⟦ As ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Sub Ξ 0 → Ctx T → Set ℓ
(⟦ ι      ⟧ᵃˢ _) σ _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) σ Γ = (⟦ D ⟧ᵃ X) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ B D ⟧ᶜ X) A Γ = Σ[ σ ∈ Sub Ξ 0 ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ Ds ⟧ X) A Γ = ∃[ D ] Σ[ x ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X) A Γ

record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public
