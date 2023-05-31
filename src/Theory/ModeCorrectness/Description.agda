{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description (SD : S.Desc)   where

open import Syntax.Simple              SD
open import Syntax.BiTyped.Description SD

private variable
  Ξ : ℕ

_∈ᵥ_ : Fin Ξ → TExps Ξ → Set
i ∈ᵥ As = L.Any (i ∈ₜ_) As

_⊆ᵥ_ : TExp Ξ → TExps Ξ → Set
A ⊆ᵥ As = ∀ {i} → i ∈ₜ A → i ∈ᵥ As

ModeCorrectᵃ : TExps Ξ → TExps Ξ → Set
ModeCorrectᵃ _  []      = ⊤
ModeCorrectᵃ As (A ∷ Δ) = A ⊆ᵥ As × ModeCorrectᵃ As Δ

module _ (A₀ : TExps Ξ) where
  Known : ArgsD Ξ → TExps Ξ
  Known []                  = A₀
  Known (_ ⊢[ Chk ] _ ∷ Ds) =     Known Ds
  Known (_ ⊢[ Inf ] A ∷ Ds) = A ∷ Known Ds

  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ []                  = ⊤
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) = let As = Known Ds in
     A ⊆ᵥ As × ModeCorrectᵃ As Δ × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Δ ⊢[ Inf ] A ∷ Ds) = let As = Known Ds in
               ModeCorrectᵃ As Δ × ModeCorrectᵃˢ Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι Chk A Ds) = ModeCorrectᵃˢ (A ∷ [])  Ds
ModeCorrectᶜ (ι Inf A Ds) = ModeCorrectᵃˢ [] ([] ⊢[ Chk ] A ∷ Ds)

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)

