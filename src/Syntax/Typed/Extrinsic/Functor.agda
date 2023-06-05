{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Extrinsic.Functor (SD : S.Desc) (Id : Set) where

open import Syntax.Simple SD

open import Syntax.NamedContext SD Id
import Syntax.Typed.Raw.Functor SD Id as R

open T SD

Pred :  (ℓ′ : Level) → (n : ℕ) → (X : Set ℓ) → Set (ℓ ⊔ lsuc ℓ′)
Pred ℓ′ n X = TExp n → Cxt n → X → Set ℓ′

Pred₀ : ℕ → (X : Set ℓ) → Set _
Pred₀ n X = Pred 0ℓ n X

private variable
  Ξ Θ   : ℕ
  A B   : TExp Ξ
  X     : Set ℓ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : Set ℓ) (P : Cxt Θ → X → Set ℓ′)
  → TSub Ξ Θ → Cxt Θ → R.⟦ Δ ⟧ᵃ X → Set ℓ′
⟦ []    ⟧ᵃ X P ρ Γ t       = P Γ t
⟦ A ∷ Δ ⟧ᵃ X P ρ Γ (x , t) = ⟦ Δ ⟧ᵃ X P ρ (x ⦂ A ⟨ ρ ⟩ , Γ) t

⟦_⟧ᵃˢ : (AD : ArgsD Ξ) (X : Set ℓ) (P : Pred ℓ′ Θ X)
  → TSub Ξ Θ → Cxt Θ → R.⟦ AD ⟧ᵃˢ X → Set ℓ′
⟦ []         ⟧ᵃˢ X _ _ _ _        = ⊤
⟦ Δ ⊢ A ∷ Ds ⟧ᵃˢ X P ρ Γ (t , ts) =
  ⟦ Δ ⟧ᵃ X (P (A ⟨ ρ ⟩)) ρ Γ t × ⟦ Ds ⟧ᵃˢ X P ρ Γ ts

⟦_⟧ᶜ : (D : ConD) → Pred ℓ′ Θ X → Pred ℓ′ Θ (R.⟦ D ⟧ᶜ X)
⟦ ι {Ξ} B D ⟧ᶜ P A Γ t = Σ[ ρ ∈ TSub Ξ _ ] B ⟨ ρ ⟩ ≡ A × ⟦ D ⟧ᵃˢ _ P ρ Γ t

⟦_⟧ : (D : Desc) → Pred ℓ′ Θ X → Pred ℓ′ Θ (R.⟦ D ⟧ X)
⟦ D ⟧ P A Γ (i , t) = ⟦ D .rules i ⟧ᶜ P A Γ t
