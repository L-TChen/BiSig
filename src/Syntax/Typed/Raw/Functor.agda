open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw.Functor (SD : S.Desc) (Id : Set) where

open import Syntax.Simple SD
open T SD

private variable
  n m : ℕ
  A B : Set

⟦_⟧ᵃ : (Δ : TExps n) → Set ℓ → Set ℓ
⟦ []    ⟧ᵃ X = X
⟦ A ∷ Δ ⟧ᵃ X = Id × ⟦ Δ ⟧ᵃ X

⟦_⟧ᵃˢ : (ADs : ArgsD n) (X : Set ℓ) → Set ℓ
⟦ []         ⟧ᵃˢ _ = ⊤
⟦ Δ ⊢ A ∷ Ds ⟧ᵃˢ X = ⟦ Δ ⟧ᵃ X × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ : (D : ConD) (X : Set ℓ) → Set ℓ
⟦ ι _ D ⟧ᶜ X = ⟦ D ⟧ᵃˢ X

⟦_⟧ : (D : Desc) (X : Set ℓ) → Set ℓ
⟦ D ⟧ X = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X
