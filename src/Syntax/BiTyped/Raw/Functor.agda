open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Functor {SD : S.Desc} (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open B {SD}

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Mode → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Set ℓ
-- ⟦ Δ ⊢ m ⦂ B ⟧ᵃ X = (Id ^ length Δ) × X m
⟦ ι m B ⟧ᵃ X = X m
⟦ A ∙ D ⟧ᵃ X = Id × ⟦ D ⟧ᵃ X

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Set ℓ
⟦ ∅      ⟧ᵃˢ _ = ⊤
⟦ D ∙ Ds ⟧ᵃˢ X = ⟦ D ⟧ᵃ X × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι Ξ Check B D ⟧ᶜ X) Check = ⟦ D ⟧ᵃˢ X
(⟦ ι Ξ Infer B D ⟧ᶜ X) Infer = ⟦ D ⟧ᵃˢ X
(⟦ ι Ξ _     B D ⟧ᶜ X) _     = ⊥

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
(⟦ Ds ⟧ X) m = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X) m