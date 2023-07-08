import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw.Functor (SD : S.Desc) where

open import Prelude

open import Syntax.Simple SD
open T SD

private variable
  n Ξ : ℕ

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = ℕ → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam 0ℓ

⟦_⟧ᵃ : (Δ : TExps Ξ) → Fam ℓ → Fam ℓ
⟦ Δ ⟧ᵃ X n = X (length Δ ʳ+ n)

⟦_⟧ᵃˢ : (ADs : ArgsD Ξ) (X : Fam ℓ) → Fam ℓ
⟦ []           ⟧ᵃˢ _ _ = ⊤
⟦ (Δ ⊢ A) ∷ Ds ⟧ᵃˢ X n = ⟦ Δ ⟧ᵃ X n × ⟦ Ds ⟧ᵃˢ X n

⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ) → Fam ℓ
⟦ ι _ D ⟧ᶜ X = ⟦ D ⟧ᵃˢ X

⟦_⟧ : (D : Desc) → Fam ℓ → Fam ℓ
⟦ D ⟧ X n = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X n
