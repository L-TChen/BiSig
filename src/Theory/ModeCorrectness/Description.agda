{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description (SD : S.Desc) (Id : Set)  where

open import Syntax.NamedContext        SD Id
open import Syntax.Simple              SD
  hiding (_++_)
open import Syntax.BiTyped.Description SD

private variable
  n : ℕ

ModeCorrectᵃ : List (Fin n) → TExps n → Set
ModeCorrectᵃ xs []      = ⊤
ModeCorrectᵃ xs (A ∷ Θ) = fv A ⊆ xs × ModeCorrectᵃ xs Θ

module _ (xs₀ : List (Fin n)) where
  Known : ArgsD n →  List (Fin n)
  Known []                     = xs₀
  Known (Θ ⊢[ Chk ] C ∷ Ds) =         Known Ds
  Known (Θ ⊢[ Inf ] C ∷ Ds) = fv C ++ Known Ds

  ModeCorrectᵃˢ : ArgsD n → Set
  ModeCorrectᵃˢ []                     = ⊤
  ModeCorrectᵃˢ (Θ ⊢[ Chk ] C ∷ Ds) = let xs = Known Ds in
    fv C ⊆ xs × ModeCorrectᵃ xs Θ × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Θ ⊢[ Inf ] C ∷ Ds) = let xs = Known Ds in
    ModeCorrectᵃ xs Θ × ModeCorrectᵃˢ Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι Chk C Ds) = ModeCorrectᵃˢ (fv C) Ds
ModeCorrectᶜ (ι Inf C Ds) = ModeCorrectᵃˢ []     ([] ⊢[ Chk ] C ∷ Ds)

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)
