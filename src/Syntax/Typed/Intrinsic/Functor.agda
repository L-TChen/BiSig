{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Intrinsic.Functor {SD : S.Desc}  where

open import Syntax.Context            SD

open import Syntax.Simple.Term        SD as Ty
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Simple.Association SD

open import Syntax.Typed.Description {SD}

Fam : (ℓ : Level) (m : ℕ) → Set (lsuc ℓ)
Fam ℓ m = TExp m → Cxt m → Set ℓ

Fam₀ = Fam lzero

private variable
  n m  : ℕ
  A B  : TExp m
  Γ Δ  : ℕ
  X Y  : Fam ℓ m

⟦_⟧ᵃ : (D : TExps n) (X : Cxt m → Set ℓ) → TSub n m → Cxt m → Set ℓ
⟦ []     ⟧ᵃ X σ Γ = X Γ
⟦ A ∷ As ⟧ᵃ X σ Γ = ⟦ As ⟧ᵃ X σ (A ⟨ σ ⟩ ∷ Γ)

⟦_⟧ᵃˢ : (D : ArgsD n) (X : Fam ℓ m) → TSub n m → Cxt m → Set ℓ
⟦ []           ⟧ᵃˢ _ _ _ = ⊤
⟦ (θ ⊢ B) ∷ Ds ⟧ᵃˢ X σ Γ = ⟦ θ ⟧ᵃ (X (B ⟨ σ ⟩)) σ Γ × ⟦ Ds ⟧ᵃˢ X σ Γ

-- the interpretation of the conclusion of a typing rule
⟦_⟧ᶜ : (D : ConD) (X : Fam ℓ m) → Fam ℓ m
⟦ ι {n} B D ⟧ᶜ X A Γ = Σ[ σ ∈ TSub n _ ] (B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X σ Γ)

⟦_⟧ : (D : Desc) (X : Fam ℓ m) → Fam ℓ m
⟦ D ⟧ X A Γ = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X A Γ

record _-Alg (D : Desc) (X : Fam ℓ m) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public
