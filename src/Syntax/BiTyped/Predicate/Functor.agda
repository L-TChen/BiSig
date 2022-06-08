open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Predicate.Functor {SD : S.Desc} (D : B.Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open B {SD}

open import Syntax.NamedContext Id

import Syntax.BiTyped.Raw.Functor   {SD} Id as R
open import Syntax.BiTyped.Raw.Term    D Id

Sub₀ : (Ξ : ℕ) → Set
Sub₀ Ξ = Sub Ξ 0

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set
  σ   : Sub₀ Ξ

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Context T → (m : Mode) → Raw m → Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) (σ : Sub₀ Ξ) (t : R.⟦ D ⟧ᵃ Raw) → Context T → Set ℓ
(⟦ ι m B ⟧ᵃ X) σ t Γ       = X (⟪ σ ⟫ B) Γ m t
(⟦ A ∙ D ⟧ᵃ X) σ (x , t) Γ = (⟦ D ⟧ᵃ X) σ t (Γ , x ⦂ ⟪ σ ⟫ A)

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) (σ : Sub₀ Ξ) (ts : R.⟦ D ⟧ᵃˢ Raw) → Context T → Set ℓ
(⟦ ι      ⟧ᵃˢ _) _ _          _ = ⊤
(⟦ ρ D Ds ⟧ᵃˢ X) σ (t , ts) Γ = (⟦ D ⟧ᵃ X) σ t Γ × (⟦ Ds ⟧ᵃˢ X) σ ts Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ) (A : T) (Γ : Context T) (m : Mode) (t : (R.⟦ D ⟧ᶜ Raw) m) → Set ℓ
(⟦ ι Ξ Check B D ⟧ᶜ X) A Γ Check t = Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ t Γ)
(⟦ ι Ξ Infer B D ⟧ᶜ X) A Γ Infer t = Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ t Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ) (A : T) (Γ : Context T) (m : Mode) (t : (R.⟦ D ⟧ Raw) m) → Set ℓ
(⟦ []     ⟧ X) _ _ _ _       = ⊥
(⟦ D ∷ Ds ⟧ X) A Γ m (inl t) = (⟦ D ⟧ᶜ X) A Γ m t
(⟦ D ∷ Ds ⟧ X) A Γ m (inr u) = (⟦ Ds ⟧ X) A Γ m u