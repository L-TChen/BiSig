{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.RawNoMode.Functor {SD : S.Desc} (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp)
open B {SD}

private variable
  Ξ   : ℕ
  m   : Mode
  A B : Set

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = Set ℓ

Fam₀ : Set₁
Fam₀ = Fam lzero

⟦_⟧ᵃ : (D : List (TExp Ξ)) → Set ℓ → Set ℓ
⟦ []    ⟧ᵃ X = X
⟦ A ∷ Θ ⟧ᵃ X = Id × ⟦ Θ ⟧ᵃ X

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : Fam ℓ) → Set ℓ
⟦ []              ⟧ᵃˢ _ = ⊤
⟦ Θ ⊢[ _ ] _ ∷ Ds ⟧ᵃˢ X = ⟦ Θ ⟧ᵃ X × ⟦ Ds ⟧ᵃˢ X

⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ) → Fam ℓ
⟦ ι _ _ Ds ⟧ᶜ X = ⟦ Ds ⟧ᵃˢ X

⟦_⟧ : (D : Desc) (X : Fam ℓ) → Fam ℓ
⟦ D ⟧ X = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X
