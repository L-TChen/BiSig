{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description (SD : S.Desc)   where

open import Syntax.Simple              SD
open import Syntax.BiTyped.Description SD

private variable
  Ξ : ℕ

_⊆ᵥ_ : TExp Ξ → TExps Ξ → Set
A ⊆ᵥ As = ∀ {i} → i ∈ᵥ A → L.Any (i ∈ᵥ_) As

ModeCorrectᵃ : TExps Ξ → TExps Ξ → Set
ModeCorrectᵃ _  []      = ⊤
ModeCorrectᵃ As (A ∷ Δ) = A ⊆ᵥ As × ModeCorrectᵃ As Δ

module _ (A₀ : TExps Ξ) where
  known : ArgsD Ξ → TExps Ξ
  known []                  = A₀
  known (_ ⊢[ Chk ] _ ∷ Ds) =     known Ds
  known (_ ⊢[ Syn ] A ∷ Ds) = A ∷ known Ds

  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ []                  = ⊤
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) = let As = known Ds in
     A ⊆ᵥ As × ModeCorrectᵃ As Δ × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) = let As = known Ds in
               ModeCorrectᵃ As Δ × ModeCorrectᵃˢ Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι Chk A Ds) = ModeCorrectᵃˢ (A ∷ []) Ds
ModeCorrectᶜ (ι Syn A Ds) = ModeCorrectᵃˢ []       ([] ⊢[ Chk ] A ∷ Ds)

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)
