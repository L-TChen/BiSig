open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Description (SD : S.Desc)  where

open import Syntax.Simple.Term      SD as Ty
  renaming (Tm₀ to T)
open import Syntax.Simple.Operation SD
open import Syntax.Typed.Context (Ty.Tm ⊥)

private variable
  n m   : ℕ
  A B   : T
  Γ Δ Ξ : Ctx
  X Y   : Fam ℓ

TExp : Ctx → Set
TExp Ξ = Tm (∃ (_∈ Ξ))

flatten : TExp Ξ → T
flatten t = ⟪ id ⟫ rename proj₁ t

ArgD : (Ξ : Ctx) → Set
ArgD Ξ = List (TExp Ξ) × TExp Ξ

infix 4 _⊢_
_⊢_ : List (TExp Ξ) → TExp Ξ → ArgD Ξ
Δ ⊢ A = Δ , A

data ArgsD (Ξ : Ctx) : Set where
  ι :                              ArgsD Ξ
  ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

data ConD (Ξ : Ctx) : Set where
  ι : (A : TExp Ξ)                 (D : ArgsD Ξ) → ConD Ξ
  σ : (D : (A : T) → ConD (A ∙ Ξ))               → ConD Ξ

infixr 6 σ
infixr 7 ρ 
syntax ι A D       = ▷ D ⦂ A
syntax σ (λ A → D) = σ[ A ] D
syntax ρ D Ds      = ρ[ D ] Ds

Desc : Set
Desc = List $ ConD ∅

⟦_⟧ᵃ : (D : ArgD Ξ) (X : Fam ℓ) → Ctx → Set ℓ
⟦ ∅      , B ⟧ᵃ X Γ = X (flatten B) Γ
⟦ A ∙ As , B ⟧ᵃ X Γ = (⟦ As , B ⟧ᵃ X) (flatten A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Ctx → Set ℓ
(⟦ ι      ⟧ᵃˢ _) _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) Γ = (⟦ D ⟧ᵃ X) Γ × (⟦ Ds ⟧ᵃˢ X) Γ

⟦_⟧ᶜ_ : (D : ConD Ξ) (X : Fam ℓ) → Fam ℓ
(⟦ ι B D ⟧ᶜ X) A Γ = flatten B ≡ A × (⟦ D ⟧ᵃˢ X) Γ
(⟦ σ D   ⟧ᶜ X) A Γ = Σ[ B ∈ T ] (⟦ D B ⟧ᶜ X) A Γ

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ ∅      ⟧ _) _ _ = ⊥
(⟦ D ∙ Ds ⟧ X) A Γ = (⟦ D ⟧ᶜ X) A Γ ⊎ (⟦ Ds ⟧ X) A Γ

record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public

-- Mode-Correct (BD : B.Desc) : Ctx → Ctx → Set
-- Complete (D : T.Desc) (BD : B.Desc) : Set