open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Description {SD : S.Desc}  where

open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)
open import Syntax.Simple.Operation {SD}
open import Syntax.Context

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Ctx T → Set ℓ

Fam₀ = Fam lzero

private variable
  A B   : T
  Γ Δ Ξ : ℕ
  X Y   : Fam ℓ

data ArgD  (Ξ : ℕ) : Set where
  ⊢_  : (B : TExp Ξ)              → ArgD Ξ
  _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

data ArgsD (Ξ : ℕ) : Set where
  ι :                               ArgsD Ξ
  ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

data ConD : Set where
  ι : (Ξ : ℕ) (A : TExp Ξ) (D : ArgsD Ξ) → ConD

infix  5 ⊢_
infixr 7 ρ 
syntax ι Ξ A D     = Ξ ▷ D ⦂ A
syntax ρ D Ds      = ρ[ D ] Ds

Desc : Set
Desc = List ConD
 
⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Sub Ξ 0 → Ctx T → Set ℓ
(⟦ ⊢    B ⟧ᵃ X) σ Γ = X (⟪ σ ⟫ B) Γ
(⟦ A ∙ As ⟧ᵃ X) σ Γ = (⟦ As ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Sub Ξ 0 → Ctx T → Set ℓ
(⟦ ι      ⟧ᵃˢ _) σ _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) σ Γ = (⟦ D ⟧ᵃ X) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ B D ⟧ᶜ X) A Γ = Σ[ σ ∈ Sub Ξ 0 ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ []           ⟧ _) _ _ = ⊥
(⟦ D ∷ Ds ⟧ X) A Γ = (⟦ D ⟧ᶜ X) A Γ ⊎ (⟦ Ds ⟧ X) A Γ

record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public

-- Mode-Correct (BD : B.Desc) : Ctx → Ctx → Set
-- Complete (D : T.Desc) (BD : B.Desc) : Set