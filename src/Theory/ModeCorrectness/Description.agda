open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description (SD : S.Desc)   where

open import Syntax.Simple              SD
open import Syntax.BiTyped.Description SD

private variable
  Ξ : ℕ

-- every variable in A is contained in some As 
Cover : Fins# Ξ → TExps Ξ → Set
Cover xs Δ = L.All (λ A → vars A #⊆ xs) Δ

known : ArgsD Ξ → Fins# Ξ
known []                = []
known (_ ⊢[ d ] A ∷ Ds) = helper d A ∪ known Ds
  where
    helper : Mode → TExp Ξ → Fins# _
    helper Chk A = []
    helper Syn A = vars A

ModeCorrectᵃ : Fins# Ξ → ArgD Ξ → Set
ModeCorrectᵃ xs (Δ ⊢[ Chk ] A) = Cover xs (A ∷ Δ)
ModeCorrectᵃ xs (Δ ⊢[ Syn ] A) = Cover xs Δ

ModeCorrectᵃˢ : Fins# Ξ → ArgsD Ξ → Set
ModeCorrectᵃˢ _  []       = ⊤
ModeCorrectᵃˢ xs (D ∷ Ds) =
  ModeCorrectᵃ (xs ∪ known Ds) D × ModeCorrectᵃˢ xs Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι {Ξ} Chk A Ds) =
  ((i : Fin Ξ) → i #∈ (vars A ∪ known Ds)) × ModeCorrectᵃˢ (vars A) Ds
ModeCorrectᶜ (ι {Ξ} Syn A Ds) =
  ((i : Fin Ξ) → i #∈ known Ds) × ModeCorrectᵃˢ []     Ds × vars A #⊆ known Ds
  -- Every i exsits in some variable of inferred types

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)
