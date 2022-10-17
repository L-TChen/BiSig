open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Syntax.BiTyped.Extrinsic.Functor {SD : S.Desc} (Id : Set) (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Sub to TSub)

open import Syntax.NamedContext   SD   Id
import Syntax.BiTyped.Raw.Functor {SD} Id as R

Pred :  (ℓ′ : Level) → (n : ℕ) → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc ℓ′))
Pred ℓ′ n X = (mod : Mode) → TExp n → Cxt n → X mod → Set ℓ′

Pred₀ : ℕ → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc lzero))
Pred₀ n X = Pred lzero n X

private variable
  n m l : ℕ
  σ     : TSub n m
  mod   : Mode
  A B   : TExp n
  X     : Mode → Set ℓ

⟦_⟧ᵃ_,_ : (Θ : List (TExp n)) (X : Mode → Set ℓ) (P : Cxt m → X mod → Set ℓ′)
  → TSub n m → Cxt m → R.⟦ Θ ⟧ᵃ X mod → Set ℓ′
(⟦ ∅     ⟧ᵃ X , P) σ Γ t       = P Γ t
(⟦ A ∙ D ⟧ᵃ X , P) σ Γ (x , t) = (⟦ D ⟧ᵃ X , P) σ (x ⦂ ⟪ σ ⟫ A , Γ) t

⟦_⟧ᵃˢ_,_ : (D : ArgsD n) (X : Mode → Set ℓ) (P : Pred ℓ′ m X)
  → TSub n m → Cxt m → R.⟦ D ⟧ᵃˢ X → Set ℓ′
(⟦ ∅               ⟧ᵃˢ X , _) _ _ _        = ⊤
(⟦ Θ ⊢[ m ] B ∙ Ds ⟧ᵃˢ X , P) σ Γ (t , ts) =
  (⟦ Θ ⟧ᵃ X , P m (⟪ σ ⟫ B)) σ Γ t × (⟦ Ds ⟧ᵃˢ X , P) σ Γ ts

⟦_⟧ᶜ_ : (D : ConD) → Pred ℓ′ m X → Pred ℓ′ m (R.⟦ D ⟧ᶜ X)
(⟦ ι {n} mod B D ⟧ᶜ P) mod′ A Γ (mod≡mod′ , t) =
  Σ[ σ ∈ TSub n _ ] ⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ _ , P) σ Γ t

⟦_⟧_ : (D : Desc) → Pred ℓ′ n X → Pred ℓ′ n (R.⟦ D ⟧ X)
(⟦ Ds ⟧ P) m A Γ (D , _ , t) = (⟦ D ⟧ᶜ P)  m A Γ t
