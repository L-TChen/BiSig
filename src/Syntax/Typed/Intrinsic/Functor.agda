open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Intrinsic.Functor {SD : S.Desc}  where

open import Syntax.Context

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
 
⟦_⟧ᵃ_ : (D : TExps n) (X : Cxt m → Set ℓ) → TSub n m → Cxt m → Set ℓ
(⟦ ∅      ⟧ᵃ X) σ Γ = X Γ
(⟦ A ∙ As ⟧ᵃ X) σ Γ = (⟦ As ⟧ᵃ X) σ (⟪ σ ⟫ A ∙ Γ) -- (⟪ σ ⟫ A ∙ Γ)

⟦_⟧ᵃˢ_ : (D : ArgsD n) (X : Fam ℓ m) → TSub n m → Cxt m → Set ℓ
(⟦ ∅            ⟧ᵃˢ _) _ _ = ⊤
(⟦ (θ ⊢ B) ∙ Ds ⟧ᵃˢ X) σ Γ = (⟦ θ ⟧ᵃ X (⟪ σ ⟫ B)) σ Γ × (⟦ Ds ⟧ᵃˢ X) σ Γ

⟦_⟧ᶜ_ : (D : ConD) (X : Fam ℓ m) → Fam ℓ m
(⟦ ι {n} B D ⟧ᶜ X) A Γ = Σ[ σ ∈ TSub n _ ] (⟪ σ ⟫ B ≡ A × (⟦ D ⟧ᵃˢ X) σ Γ)

⟦_⟧_ : (D : Desc) (X : Fam ℓ m) → Fam ℓ m
(⟦ Ds ⟧ X) A Γ = ∃[ D ] Σ[ x ∈ (D ∈ Ds) ] (⟦ D ⟧ᶜ X) A Γ

record _-Alg (D : Desc) (X : Fam ℓ m) : Set ℓ where
  field
    var : _∈_     ⇒ X
    alg : ⟦ D ⟧ X ⇒ X
open _-Alg public
