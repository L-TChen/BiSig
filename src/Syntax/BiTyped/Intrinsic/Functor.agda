{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Intrinsic.Functor {SD : S.Desc} where

open import Syntax.Context     SD
open import Syntax.Simple.Term SD as Ty
  renaming (Tm to TExp)

open import Syntax.BiTyped.Description SD

Fam : (m : ℕ) (ℓ : Level) → Set (lsuc ℓ)
Fam m ℓ = Mode → TExp m → Cxt m → Set ℓ

Fam₀ : ℕ → Set₁
Fam₀ m = Fam m lzero

private variable
  n m : ℕ
  mod : Mode
  X Y : Fam m ℓ
  Γ   : Cxt m
  A B : TExp m

⟦_⟧ᵃ : List (TExp n) → (Cxt m → Set ℓ) → Sub n m → Cxt m → Set ℓ
⟦ []    ⟧ᵃ X _ Γ = X Γ
⟦ A ∷ D ⟧ᵃ X σ Γ = ⟦ D ⟧ᵃ X σ (A ⟨ σ ⟩ ∷ Γ)

⟦_⟧ᵃˢ : (D : ArgsD n) (X : Fam m ℓ) → Sub n m → Cxt m → Set ℓ
⟦ []              ⟧ᵃˢ _ σ _ = ⊤
⟦ Δ ⊢[ m ] B ∷ Ds ⟧ᵃˢ X σ Γ = ⟦ Δ ⟧ᵃ (X m (B ⟨ σ ⟩)) σ Γ × ⟦ Ds ⟧ᵃˢ X σ Γ

⟦_⟧ᶜ : (D : ConD) (X : Fam m ℓ) → Fam m ℓ
⟦ ι m₀ B D ⟧ᶜ X m A Γ = m₀ ≡ m × Σ[ σ ∈ Sub _ _ ] (B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X σ Γ)

⟦_⟧ : (D : Desc) (X : Fam m ℓ) → Fam m ℓ
⟦ D ⟧ X m A Γ = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X m A Γ

record _-Alg (D : Desc) (X : Fam m ℓ) : Set ℓ where
  field
    var     : _∈_     ⇒ X Infer
    toInfer : X Check ⇒ X Infer
    toCheck : X Infer ⇒ X Check
    alg : ⟦ D ⟧ X mod ⇒ X mod
open _-Alg public
