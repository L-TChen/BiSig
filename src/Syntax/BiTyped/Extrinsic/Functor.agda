{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Functor (SD : S.Desc) (Id : Set) where

open import Syntax.Simple SD

open import Syntax.NamedContext   SD Id
import Syntax.BiTyped.Raw.Functor SD Id as R

open B SD

Pred :  (ℓ′ : Level) → ℕ → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc ℓ′))
Pred ℓ′ Θ X = (d : Mode) → TExp Θ → Cxt Θ → X d → Set ℓ′

Pred₀ : ℕ → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc lzero))
Pred₀ Θ X = Pred lzero Θ X

private variable
  Ξ Θ : ℕ
  ρ   : TSub Ξ Θ
  d   : Mode
  X   : Mode → Set ℓ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : Mode → Set ℓ) (P : Cxt Θ → X d → Set ℓ′)
  → TSub Ξ Θ → Cxt Θ → R.⟦ Δ ⟧ᵃ (X d) → Set ℓ′
⟦ []    ⟧ᵃ X P ρ Γ t       = P Γ t
⟦ A ∷ Δ ⟧ᵃ X P ρ Γ (x , t) = ⟦ Δ ⟧ᵃ X P ρ (x ⦂ A ⟨ ρ ⟩ , Γ) t

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : Mode → Set ℓ) (P : Pred ℓ′ Θ X)
  → TSub Ξ Θ → Cxt Θ → R.⟦ D ⟧ᵃˢ X → Set ℓ′
⟦ []              ⟧ᵃˢ X _ _ _ _        = ⊤
⟦ Δ ⊢[ d ] A ∷ Ds ⟧ᵃˢ X P ρ Γ (t , ts) =
  ⟦ Δ ⟧ᵃ X (P d (A ⟨ ρ ⟩)) ρ Γ t × ⟦ Ds ⟧ᵃˢ X P ρ Γ ts

⟦_⟧ᶜ : (D : ConD) → Pred ℓ′ Θ X → Pred ℓ′ Θ (R.⟦ D ⟧ᶜ X)
⟦ ι {Ξ} d A D ⟧ᶜ P d′ A₀ Γ (d≡d′ , t) =
  Σ[ σ ∈ TSub Ξ _ ] A ⟨ σ ⟩ ≡ A₀ × ⟦ D ⟧ᵃˢ _ P σ Γ t

⟦_⟧ : (D : Desc) → Pred ℓ′ Θ X → Pred ℓ′ Θ (R.⟦ D ⟧ X)
⟦ D ⟧ P Θ A Γ (i , t) = ⟦ D .rules i ⟧ᶜ P Θ A Γ t
