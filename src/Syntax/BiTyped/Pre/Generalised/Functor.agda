{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Pre.Generalised.Functor (SD : S.Desc) where

open import Syntax.Simple              SD
import      Syntax.Typed.Raw.Functor   SD as R
open import Syntax.BiTyped.Description SD

open import Theory.Erasure.Description

private variable
  Ξ : ℕ
  X : R.Fam ℓ

Fam : (ℓ : Level) → R.Fam ℓ′ → Set (lmax (lsuc ℓ) ℓ′)
Fam ℓ X = (valid exact : Bool) → Mode → {n : ℕ} → X n → Set ℓ

Fam₀ : R.Fam₀ → Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
     → (valid : Bool) → Mode → {n : ℕ} → R.⟦ Δ ⟧ᵃ X n → Set ℓ′
⟦ Δ ⟧ᵃ X Y v d x = ∃[ e ] Y v e d x

⟦_⟧ᵃˢ : (Ds : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
      → (vs : Vec Bool (length Ds)) → {n : ℕ} → R.⟦ eraseᵃˢ Ds ⟧ᵃˢ X n → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _        _        = ⊤
⟦ (Δ ⊢[ d ] _) ∷ Ds ⟧ᵃˢ X Y (v ∷ vs) (x , xs) = ⟦ Δ ⟧ᵃ X Y v d x × ⟦ Ds ⟧ᵃˢ X Y vs xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
     → (valid : Bool) → Mode → {n : ℕ} → R.⟦ eraseᶜ D ⟧ᶜ X n → Set ℓ′
⟦ ι d  _ Ds ⟧ᶜ X Y v d' ts = ∃[ vs ] And (toList vs) v × d ≡ d' × ⟦ Ds ⟧ᵃˢ X Y vs ts

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y v e d (i , xs) = e ≡ true × ⟦ D .rules i ⟧ᶜ X Y v d xs
