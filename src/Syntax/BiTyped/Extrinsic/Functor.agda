open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Syntax.BiTyped.Extrinsic.Functor {SD : S.Desc} (Id : Set) (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.NamedContext   Id
import Syntax.BiTyped.Raw.Functor {SD} Id as R


Pred :  (ℓ′ : Level) → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc ℓ′))
Pred ℓ′ X = (m : Mode) → T → Context T → X m → Set ℓ′

Pred₀ : (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc lzero))
Pred₀ X = Pred lzero X

private variable
  Ξ   : ℕ
  m   : Mode
  A B : T
  X   : Mode → Set ℓ
  σ   : Sub₀ Ξ

⟦_⟧ᵃ_,_ : (Θ : List (TExp Ξ)) (X : Mode → Set ℓ) (P : Context T → X m → Set ℓ′)
  → Sub₀ Ξ → Context T → R.⟦ Θ ⟧ᵃ X m → Set ℓ′
(⟦ ∅     ⟧ᵃ X , P) σ Γ t       = P Γ t
(⟦ A ∙ D ⟧ᵃ X , P) σ Γ (x , t) = (⟦ D ⟧ᵃ X , P) σ (x ⦂ ⟪ σ ⟫ A , Γ) t

⟦_⟧ᵃˢ_,_ : (D : ArgsD Ξ) (X : Mode → Set ℓ) (P : Pred ℓ′ X)
  → Sub₀ Ξ → Context T → R.⟦ D ⟧ᵃˢ X → Set ℓ′
(⟦ ∅               ⟧ᵃˢ X , _) _ _ _        = ⊤
(⟦ Θ ⊢[ m ] B ∙ Ds ⟧ᵃˢ X , P) σ Γ (t , ts) = (⟦ Θ ⟧ᵃ X , P m (⟪ σ ⟫ B)) σ Γ t × (⟦ Ds ⟧ᵃˢ X , P) σ Γ ts

⟦_⟧ᶜ_ : (D : ConD) (P : Pred ℓ′ X) (m : Mode) (A : T) (Γ : Context T) (t : (R.⟦ D ⟧ᶜ X) m) → Set ℓ′
(⟦ ι Check B D ⟧ᶜ P) Check A Γ t = Σ[ σ ∈ Sub₀ _ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ _ , P) σ Γ t)
(⟦ ι Infer B D ⟧ᶜ P) Infer A Γ t = Σ[ σ ∈ Sub₀ _ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ _ , P) σ Γ t)

⟦_⟧_ : (D : Desc) (P : Pred ℓ′ X) (m : Mode) (A : T) (Γ : Context T) (t : (R.⟦ D ⟧ X) m) → Set ℓ′
(⟦ Ds ⟧ P) m A Γ (D , _ , t) = (⟦ D ⟧ᶜ P)  m A Γ t