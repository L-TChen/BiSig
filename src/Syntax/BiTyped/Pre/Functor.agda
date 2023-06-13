{-# OPTIONS --safe #-}

import Syntax.Simple.Description as S

module Syntax.BiTyped.Pre.Functor (SD : S.Desc) where

open import Prelude

open import Syntax.Simple              SD
import      Syntax.Typed.Raw.Functor   SD as R
open import Syntax.BiTyped.Description SD

open import Theory.Erasure

private variable
  Ξ : ℕ
  X : R.Fam ℓ

Fam : (ℓ : Level) → R.Fam ℓ′ → Set (lsuc ℓ ⊔ ℓ′)
Fam ℓ X = Mode → {n : ℕ} → X n → Set ℓ

Fam₀ : R.Fam₀ → Set₁
Fam₀ = Fam 0ℓ

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ Δ ⟧ᵃ X)
⟦ Δ ⟧ᵃ X Y d x = Y d x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → {n : ℕ} → R.⟦ eraseᵃˢ D ⟧ᵃˢ X n → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _        = ⊤
⟦ (Δ ⊢[ d ] _) ∷ Ds ⟧ᵃˢ X Y (x , xs) = ⟦ Δ ⟧ᵃ X Y d x × ⟦ Ds ⟧ᵃˢ X Y xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι d  _ D ⟧ᶜ X Y d' xs = d ≡ d' × ⟦ D ⟧ᵃˢ X Y xs

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y d (i , xs) = ⟦ D .rules i ⟧ᶜ X Y d xs
