{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.HasMode.Functor (SD : S.Desc) where

open import Syntax.Simple              SD
import      Syntax.Typed.Raw.Functor   SD as R
open import Syntax.BiTyped.Description SD

open import Theory.Erasure.Description

private variable
  Ξ : ℕ
  X : R.Fam ℓ

Fam : (ℓ : Level) → R.Fam ℓ′ → Set (lmax (lsuc ℓ) ℓ′)
Fam ℓ X = (n : ℕ) → Mode → X n → Set ℓ

Fam₀ : R.Fam₀ → Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ Δ ⟧ᵃ X)
⟦ Δ ⟧ᵃ X Y n d x = Y (length Δ ʳ+ n) d x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → (n : ℕ) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X n → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _ _        = ⊤
⟦ (Δ ⊢[ d ] _) ∷ Ds ⟧ᵃˢ X Y n (x , xs) = ⟦ Δ ⟧ᵃ X Y n d x × ⟦ Ds ⟧ᵃˢ X Y n xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι d  _ D ⟧ᶜ X Y n d' t = d ≡ d' × ⟦ D ⟧ᵃˢ X Y n t

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y n d (i , t) = ⟦ D .rules i ⟧ᶜ X Y n d t
