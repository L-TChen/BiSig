open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Description {SD : S.Desc}  where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open B {SD} hiding (⟦_⟧ᵃ_; ⟦_⟧ᵃˢ_; ⟦_⟧ᶜ_; ⟦_⟧_; Fam; Fam₀)

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Set ℓ → Mode → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Set ℓ → Set ℓ
(⟦ ι m B ⟧ᵃ X) Id = X Id m
(⟦ A ∙ D ⟧ᵃ X) Id = Id × (⟦ D ⟧ᵃ X) Id

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Set ℓ → Set ℓ
(⟦ ι      ⟧ᵃˢ _) _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) Id = (⟦ D ⟧ᵃ X) Id × (⟦ Ds ⟧ᵃˢ X) Id

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ Check B D ⟧ᶜ X) Id Check = (⟦ D ⟧ᵃˢ X) Id
(⟦ ι Ξ Infer B D ⟧ᶜ X) Id Infer = (⟦ D ⟧ᵃˢ X) Id
(⟦ ι Ξ Infer B D ⟧ᶜ X) Id Check = ⊥
(⟦ ι Ξ Check B D ⟧ᶜ X) Id Infer = ⊥

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ []     ⟧ X) m Id = ⊥
(⟦ D ∷ Ds ⟧ X) m Id = (⟦ D ⟧ᶜ X) m Id ⊎ (⟦ Ds ⟧ X) m Id