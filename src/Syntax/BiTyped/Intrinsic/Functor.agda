open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Intrinsic.Functor {SD : S.Desc} where

open import Syntax.Context  SD
open import Syntax.Simple   SD

open import Syntax.BiTyped.Description SD

Fam : (Θ : ℕ) (ℓ : Level) → Set (lsuc ℓ)
Fam Θ ℓ = Mode → TExp Θ → Cxt Θ → Set ℓ

Fam₀ : ℕ → Set₁
Fam₀ Θ = Fam Θ 0ℓ

private variable
  Ξ Θ : ℕ
  d : Mode
  X Y : Fam Θ ℓ
  Γ   : Cxt Θ
  A B : TExp Θ

⟦_⟧ᵃ : TExps Ξ → (Cxt Θ → Set ℓ) → TSub Ξ Θ → Cxt Θ → Set ℓ
⟦ []    ⟧ᵃ X _ Γ = X Γ
⟦ A ∷ Δ ⟧ᵃ X ρ Γ = ⟦ Δ ⟧ᵃ X ρ (A ⟨ ρ ⟩ ∷ Γ)

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : Fam Θ ℓ) → TSub Ξ Θ → Cxt Θ → Set ℓ
⟦ []              ⟧ᵃˢ _ ρ _ = ⊤
⟦ Δ ⊢[ m ] B ∷ Ds ⟧ᵃˢ X ρ Γ = ⟦ Δ ⟧ᵃ (X m (B ⟨ ρ ⟩)) ρ Γ × ⟦ Ds ⟧ᵃˢ X ρ Γ

⟦_⟧ᶜ : (D : ConD) (X : Fam Θ ℓ) → Fam Θ ℓ
⟦ ι d₀ B D ⟧ᶜ X d A Γ = d₀ ≡ d × Σ[ ρ ∈ TSub _ _ ] (B ⟨ ρ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X ρ Γ)

⟦_⟧ : (D : Desc) (X : Fam Θ ℓ) → Fam Θ ℓ
⟦ D ⟧ X Θ A Γ = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X Θ A Γ

record _-Alg (D : Desc) (X : Fam Θ ℓ) : Set ℓ where
  field
    var   : _∈_       ⇒ X Syn
    toSyn : X Chk     ⇒ X Syn
    toChk : X Syn     ⇒ X Chk
    alg   : ⟦ D ⟧ X d ⇒ X d
open _-Alg public
