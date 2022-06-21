open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.RawNoMode.Functor {SD : S.Desc} (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open B {SD}

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ_ : (D : List (TExp Ξ)) → Set ℓ → Set ℓ
⟦ ∅     ⟧ᵃ X = X
⟦ A ∙ Θ ⟧ᵃ X = Id × ⟦ Θ ⟧ᵃ X

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Set ℓ
⟦ ∅      ⟧ᵃˢ _ = ⊤
⟦ Θ ⊢[ _ ] _ ∙ Ds ⟧ᵃˢ X = ⟦ Θ ⟧ᵃ X × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) → Fam ℓ
(⟦ ι _ _ D ⟧ᶜ X) = ⟦ D ⟧ᵃˢ X

⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
⟦ Ds ⟧ X = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X)