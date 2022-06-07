open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description where

data Mode : Set where
  Check Infer : Mode

module _ {SD : S.Desc} where
  open import Syntax.Simple.Term SD as Ty
    renaming (Tm₀ to T)
  open import Syntax.Context    T

  Fam : (ℓ : Level) → Set (lsuc ℓ)
  Fam ℓ = Mode → T → Ctx → Set ℓ

  Fam₀ = Fam lzero

  private variable
    m     : Mode
    A B   : T
    Γ Δ Ξ : Ctx
    X Y   : Fam ℓ

  data ArgD  (Ξ : Ctx) : Set where
    ι   : (m : Mode)   (B : TExp Ξ) → ArgD Ξ
    _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

  infixr 5 ⇉_ ⇇_
  ⇉_ ⇇_ : TExp Ξ → ArgD Ξ
  ⇉_ = ι Infer
  ⇇_ = ι Check

  data ArgsD (Ξ : Ctx) : Set where
    ι :                               ArgsD Ξ
    ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

  data ConD (Ξ : Ctx) : Set where
    ι : (m : Mode)                   (A : TExp Ξ) (D : ArgsD Ξ) → ConD Ξ
    σ : (D : (A : T) → ConD (A ∙ Ξ))                            → ConD Ξ

  infixr 6 σ ▷_⇉_ ▷_⇇_
  infixr 7 ρ 

  ▷_⇉_ : (D : ArgsD Ξ) (A : TExp Ξ) → ConD Ξ
  ▷ D ⇉ A = ι Infer A D

  ▷_⇇_ : (D : ArgsD Ξ) (A : TExp Ξ) → ConD Ξ
  ▷ D ⇇ A = ι Check A D

  syntax σ (λ A → D) = σ[ A ] D
  syntax ρ D Ds      = ρ[ D ] Ds

  Desc : Set
  Desc = List $ ConD ∅

  ⟦_⟧ᵃ_ : (D : ArgD Ξ) (X : Fam ℓ) → Ctx → Set ℓ
  (⟦ ι m B ⟧ᵃ X) Γ = X m (flatten B) Γ
  (⟦ A ∙ D ⟧ᵃ X) Γ = (⟦ D ⟧ᵃ X) (flatten A ∙ Γ)

  ⟦_⟧ᵃˢ_ : (D : ArgsD Ξ) (X : Fam ℓ) → Ctx → Set ℓ
  (⟦ ι      ⟧ᵃˢ _) _ = ⊤
  (⟦ ρ D Ds ⟧ᵃˢ X) Γ = (⟦ D ⟧ᵃ X) Γ × (⟦ Ds ⟧ᵃˢ X) Γ

  ⟦_⟧ᶜ_ : (D : ConD Ξ) (X : Fam ℓ) → Fam ℓ
  (⟦ ι m B D ⟧ᶜ X) m′ A Γ = flatten B ≡ A × m ≡ m′ × (⟦ D ⟧ᵃˢ X) Γ
  (⟦ σ D     ⟧ᶜ X) m  A Γ = Σ[ B ∈ T ] (⟦ D B ⟧ᶜ X) m A Γ

  ⟦_⟧_ : (D : Desc) (X : Fam ℓ) → Fam ℓ
  (⟦ []      ⟧ _) m _ _ = ⊥
  (⟦ D ∷ Ds ⟧ X)  m A Γ = (⟦ D ⟧ᶜ X) m A Γ ⊎ (⟦ Ds ⟧ X) m A Γ

  record _-Alg (D : Desc) (X : Fam ℓ) : Set ℓ where
    field
      var     : _∈_         ⇒ X Infer
      toInfer : X Check     ⇒ X Infer
      toCheck : X Infer     ⇒ X Check
      alg     : (⟦ D ⟧ X) m ⇒ X m
  open _-Alg public
