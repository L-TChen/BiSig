open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description {SD : S.Desc} (Id : Set)  where

open import Syntax.NamedContext Id
open import Syntax.Simple.Term  SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T)
open import Syntax.Simple.Properties         {SD}
open import Syntax.BiTyped.Description       {SD}
open import Data.List.Relation.Binary.Subset.Propositional

private variable
  Ξ     : ℕ

ModeCorrectᵃ : List (Fin Ξ) → TExps Ξ → Set
ModeCorrectᵃ xs ∅       = ⊤
ModeCorrectᵃ xs (A ∙ Θ) = fv A ⊆ xs × ModeCorrectᵃ xs Θ

module _ (xs₀ : List (Fin Ξ)) where
  Known : ArgsD Ξ →  List (Fin Ξ)
  Known ∅                     = xs₀
  Known (Θ ⊢[ Check ] C ∙ Ds) =         Known Ds
  Known (Θ ⊢[ Infer ] C ∙ Ds) = fv C ++ Known Ds

  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ ∅                     = ⊤
  ModeCorrectᵃˢ (Θ ⊢[ Check ] C ∙ Ds) = let xs = Known Ds in
    fv C ⊆ xs × ModeCorrectᵃ xs Θ × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Θ ⊢[ Infer ] C ∙ Ds) = let xs = Known Ds in
    ModeCorrectᵃ xs Θ × ModeCorrectᵃˢ Ds

ModeCorrect : Desc → Set
ModeCorrect = All λ
  where (ι Check C Ds) → ModeCorrectᵃˢ (fv C) Ds
        (ι Infer C Ds) → ModeCorrectᵃˢ ∅      (∅ ⊢[ Check ] C ∙ Ds)