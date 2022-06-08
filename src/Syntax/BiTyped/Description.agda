open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description {SD : S.Desc} where

open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)

open import Syntax.Context

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Mode → T → Ctx T → Set ℓ

Fam₀ = Fam lzero

Sub₀ : ℕ → Set
Sub₀ Ξ = Sub Ξ 0

private variable
  m   : Mode
  A B : T
  Ξ   : ℕ
  Γ Δ : Ctx T
  X Y : Fam ℓ

infixr 5 ⇉_ ⇇_
infix  6 _▷_⇉_ _▷_⇇_
infixr 7 ρ 
syntax ρ D Ds      = ρ[ D ] Ds

data ArgD  (Ξ : ℕ) : Set where
  ι   : (m : Mode)   (B : TExp Ξ) → ArgD Ξ
  _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

data ArgsD (Ξ : ℕ) : Set where
  ι :                               ArgsD Ξ
  ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

data ConD : Set where
  ι :  (Ξ : ℕ) (m : Mode) (A : TExp Ξ) (D : ArgsD Ξ) → ConD

Desc : Set
Desc = List ConD

⇉_ ⇇_ : TExp Ξ → ArgD Ξ
⇉_ = ι Infer
⇇_ = ι Check

_▷_⇉_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇉ A = ι Ξ Infer A D

_▷_⇇_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇇ A = ι Ξ Check A D

⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ι m B ⟧ᵃ X) σ Γ = X m (⟪ σ ⟫ B) Γ
(⟦ A ∙ D ⟧ᵃ X) σ Γ = (⟦ D ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Sub₀ Ξ → Ctx T → Set ℓ
(⟦ ι      ⟧ᵃˢ _) σ _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) σ Γ = (⟦ D ⟧ᵃ X) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ m B D ⟧ᶜ X) m′ A Γ = m ≡ m′ × Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ []      ⟧ _) m _ _ = ⊥
(⟦ D ∷ Ds ⟧ X)  m A Γ = (⟦ D ⟧ᶜ X) m A Γ ⊎ (⟦ Ds ⟧ X) m A Γ
