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

Cover : TExps Ξ → TExps Ξ → Set
Cover As = All (_⊆ᵥ As)

module Chk where
  ModeCorrectᵃˢ : ArgsD Ξ → TExps Ξ × Set → TExps Ξ × Set
  ModeCorrectᵃˢ []                  (As , MC) = As , MC
  ModeCorrectᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) (As , MC) =
    ModeCorrectᵃˢ Ds (A ∷ As , (Cover As Δ × MC))
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) (As , MC) =
    ModeCorrectᵃˢ Ds (As , (Cover As (A ∷ Δ) × MC))

module Syn where 
  known : ArgsD Ξ → TExps Ξ
  known []                  = []
  known (_ ⊢[ Chk ] A ∷ Ds) =     known Ds
  known (_ ⊢[ Syn ] A ∷ Ds) = A ∷ known Ds

  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ []       = ⊤
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) = Cover (known Ds) (A ∷ Δ) × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) = Cover (known Ds) Δ       × ModeCorrectᵃˢ Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι Chk A Ds) = Chk.ModeCorrectᵃˢ Ds (A ∷ [] , ⊤) .proj₂
ModeCorrectᶜ (ι Syn A Ds) = A ⊆ᵥ (Syn.known Ds) × Syn.ModeCorrectᵃˢ Ds

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)


Tightᶜ : ConD → Set
Tightᶜ (ι {Ξ} Chk A Ds) =
  (i : Fin Ξ) → L.Any (i ∈ᵥ_) (A ∷ Syn.known Ds)
Tightᶜ (ι {Ξ} Syn A Ds) =
  (i : Fin Ξ) → L.Any (i ∈ᵥ_) (Syn.known Ds)
  -- Every i exsits in some variable of inferred types
