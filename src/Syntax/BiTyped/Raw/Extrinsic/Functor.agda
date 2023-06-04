{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Raw.Extrinsic.Functor (SD : S.Desc) where

open import Syntax.Simple              SD
open import Syntax.BiTyped.Description SD
import Syntax.Typed.Raw.Functor        SD as R

open import Theory.Erasure.Description

private variable
  n Ξ : ℕ
  X   : R.Fam ℓ

Fam : (ℓ : Level) → R.Fam ℓ′ → Set (lmax (lsuc ℓ) ℓ′)
Fam ℓ X = (n : ℕ) → Mode → X n → Set ℓ

Fam₀ : R.Fam₀ → Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (Δ : TExps Ξ) → Fam ℓ X → Fam ℓ (R.⟦ Δ ⟧ᵃ X)
⟦ Δ ⟧ᵃ X n d x = X (length Δ ʳ+ n) d x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) → Fam ℓ X → (n : ℕ) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X n → Set ℓ
⟦ []                ⟧ᵃˢ _ _ _        = ⊤
⟦ (Δ ⊢[ d ] _) ∷ Ds ⟧ᵃˢ X n (x , xs) = ⟦ Δ ⟧ᵃ X n d x × ⟦ Ds ⟧ᵃˢ X n xs

⟦_⟧ᶜ : (D : ConD) → Fam ℓ X → Fam ℓ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι d  _ D ⟧ᶜ X n d' t = d ≡ d' × ⟦ D ⟧ᵃˢ X n t

⟦_⟧ : (D : Desc) → Fam ℓ X → Fam ℓ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X n d (i , t) = ⟦ D .rules i ⟧ᶜ X n d t
