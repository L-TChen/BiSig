{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Intrinsic.Functor {SD : S.Desc}  where

open import Syntax.Context            SD

open import Syntax.Simple             SD as Ty
open import Syntax.Simple.Association SD

open import Syntax.Typed.Description  SD

Fam : (ℓ : Level) (m : ℕ) → Set (lsuc ℓ)
Fam ℓ m = TExp m → Cxt m → Set ℓ

Fam₀ = Fam lzero

private variable
  Ξ Θ  : ℕ
  A B  : TExp Θ
  Γ Δ  : ℕ
  X Y  : Fam ℓ Θ

⟦_⟧ᵃ : (D : TExps Ξ) (X : Cxt Θ → Set ℓ) → TSub Ξ Θ → Cxt Θ → Set ℓ
⟦ []     ⟧ᵃ X σ Γ = X Γ
⟦ A ∷ As ⟧ᵃ X σ Γ = ⟦ As ⟧ᵃ X σ (A ⟨ σ ⟩ ∷ Γ)

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : Fam ℓ Θ) → TSub Ξ Θ → Cxt Θ → Set ℓ
⟦ []           ⟧ᵃˢ _ _ _ = ⊤
⟦ (θ ⊢ B) ∷ Ds ⟧ᵃˢ X σ Γ = ⟦ θ ⟧ᵃ (X (B ⟨ σ ⟩)) σ Γ × ⟦ Ds ⟧ᵃˢ X σ Γ

-- the interpretation of the conclusion of a typing rule
⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ Θ) → Fam ℓ Θ
⟦ ι {Ξ} A D ⟧ᶜ X A₀ Γ = Σ[ ρ ∈ TSub Ξ _ ] (A ⟨ ρ ⟩ ≡ A₀ × ⟦ D ⟧ᵃˢ X ρ Γ)

⟦_⟧ : (D : Desc) (X : Fam ℓ Θ) → Fam ℓ Θ
⟦ D ⟧ X A Γ = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X A Γ

record _-Alg (D : Desc) (X : Fam ℓ Θ) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public
