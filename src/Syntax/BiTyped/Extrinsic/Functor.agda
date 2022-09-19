open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Syntax.BiTyped.Extrinsic.Functor {SD : S.Desc} (Id : Set) (D : Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp)

open import Syntax.NamedContext   Id
import Syntax.BiTyped.Raw.Functor {SD} Id as R

Cxt : ℕ → Set
Cxt m = Context (TExp m)

Pred :  (ℓ′ : Level) → (n : ℕ) → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc ℓ′))
Pred ℓ′ n X = (mod : Mode) → TExp n → Cxt n → X mod → Set ℓ′

Pred₀ : ℕ → (X : Mode → Set ℓ) → Set (lmax ℓ (lsuc lzero))
Pred₀ n X = Pred lzero n X

private variable
  n m l : ℕ
  σ     : Sub n m
  mod   : Mode
  A B   : TExp n
  X     : Mode → Set ℓ

⟦_⟧ᵃ_,_ : (Θ : List (TExp n)) (X : Mode → Set ℓ) (P : Cxt m → X mod → Set ℓ′)
  → Sub n m → Cxt m → R.⟦ Θ ⟧ᵃ X mod → Set ℓ′
(⟦ ∅     ⟧ᵃ X , P) σ Γ t       = P Γ t
(⟦ A ∙ D ⟧ᵃ X , P) σ Γ (x , t) = (⟦ D ⟧ᵃ X , P) σ (x ⦂ ⟪ σ ⟫ A , Γ) t

⟦_⟧ᵃˢ_,_ : (D : ArgsD n) (X : Mode → Set ℓ) (P : Pred ℓ′ m X)
  → Sub n m → Cxt m → R.⟦ D ⟧ᵃˢ X → Set ℓ′
(⟦ ∅               ⟧ᵃˢ X , _) _ _ _        = ⊤
(⟦ Θ ⊢[ m ] B ∙ Ds ⟧ᵃˢ X , P) σ Γ (t , ts) =
  (⟦ Θ ⟧ᵃ X , P m (⟪ σ ⟫ B)) σ Γ t × (⟦ Ds ⟧ᵃˢ X , P) σ Γ ts

⟦_⟧ᶜ_ : (D : ConD) (P : Pred ℓ′ m X) (mod : Mode) (A : TExp m) (Γ : Cxt m)
  (t : (R.⟦ D ⟧ᶜ X) mod) → Set ℓ′
(⟦ ι mod B D ⟧ᶜ P) mod′ A Γ (refl , t) = Σ[ σ ∈ Sub _ _ ] ⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ _ , P) σ Γ t

⟦_⟧_ : (D : Desc) (P : Pred ℓ′ m X) (mod : Mode) (A : TExp m) (Γ : Cxt m)
  (t : (R.⟦ D ⟧ X) mod) → Set ℓ′
(⟦ Ds ⟧ P) m A Γ (D , _ , t) = (⟦ D ⟧ᶜ P)  m A Γ t
