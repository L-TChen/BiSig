open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Syntax.BiTyped.Extrinsic.Functor {SD : S.Desc} (Id : Set) (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.NamedContext   Id
import Syntax.BiTyped.Raw.Functor {SD} Id as R

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set
  X   : Mode → Set ℓ
  σ   : Sub₀ Ξ

Pred : (X : Mode → Set ℓ) (ℓ′ : Level) → Set (lmax ℓ (lsuc ℓ′))
Pred X ℓ′ = T → Context T → (m : Mode) → X m → Set ℓ′

Pred₀ : (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc lzero))
Pred₀ X = Pred X lzero

⟦_⟧ᵃ_ : (D : ArgD Ξ) (P : Pred X ℓ′) (σ : Sub₀ Ξ) (Γ : Context T) (t : R.⟦ D ⟧ᵃ X) → Set ℓ′
(⟦ ι m B ⟧ᵃ X) σ Γ t       = X (⟪ σ ⟫ B) Γ m t
(⟦ A ∙ D ⟧ᵃ X) σ Γ (x , t) = (⟦ D ⟧ᵃ X) σ (x ⦂ ⟪ σ ⟫ A , Γ) t

⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (P : Pred X ℓ′) (σ : Sub₀ Ξ) (Γ : Context T) (ts : R.⟦ D ⟧ᵃˢ X) → Set ℓ′
(⟦ ∅      ⟧ᵃˢ _) _ _ _        = ⊤
(⟦ D ∙ Ds ⟧ᵃˢ X) σ Γ (t , ts) = (⟦ D ⟧ᵃ X) σ Γ t × (⟦ Ds ⟧ᵃˢ X) σ Γ ts

⟦_⟧ᶜ_ : (D : ConD) (P : Pred X ℓ′) (m : Mode) (A : T) (Γ : Context T) (t : (R.⟦ D ⟧ᶜ X) m) → Set ℓ′
(⟦ ι Ξ Check B D ⟧ᶜ X) Check A Γ t = Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ t)
(⟦ ι Ξ Infer B D ⟧ᶜ X) Infer A Γ t = Σ[ σ ∈ Sub₀ Ξ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ t)

⟦_⟧_ : (D : Desc) (P : Pred X ℓ′) (m : Mode) (A : T) (Γ : Context T) (t : (R.⟦ D ⟧ X) m) → Set ℓ′
(⟦ Ds ⟧ X) m A Γ (D , i , t) = (⟦ D ⟧ᶜ X)  m A Γ t