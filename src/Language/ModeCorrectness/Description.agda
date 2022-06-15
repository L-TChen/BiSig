open import Prelude

import Syntax.Simple.Description  as S

module Language.ModeCorrectness.Description {SD : S.Desc} (Id : Set)  where

open import Syntax.NamedContext Id
open import Syntax.Simple.Term  SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T)
open import Syntax.Simple.Properties         {SD}
open import Syntax.BiTyped.Description       {SD}
open import Data.List.Relation.Binary.Subset.Propositional

private variable
  Ξ     : ℕ
  m     : Mode
  xs    : List (Fin Ξ)
  D     : ArgD Ξ
  Ds    : ArgsD Ξ

ModeCorrectᵃ : List (Fin Ξ) → TExps Ξ → Set
ModeCorrectᵃ xs ∅       = ⊤
ModeCorrectᵃ xs (A ∙ Θ) = fv A ⊆ xs × ModeCorrectᵃ xs Θ

module _ (xs₀ : List (Fin Ξ)) where
  data ModeCorrectᵃˢ : List (Fin Ξ) → ArgsD Ξ → Set where
    nil
      : ModeCorrectᵃˢ xs₀ ∅
    cons⇉
      : (Θ : TExps Ξ) (C : TExp Ξ) (Ds : ArgsD Ξ)
      → (SD : ModeCorrectᵃ xs Θ) (SDs : ModeCorrectᵃˢ xs Ds) 
      → ModeCorrectᵃˢ (fv C ++ xs) (Θ ⊢[ Infer ] C ∙ Ds)
    cons⇇
      : (Θ : TExps Ξ) (C : TExp Ξ) (fvD⊆xs : fv C ⊆ xs) (Ds : ArgsD Ξ)
      → (SD : ModeCorrectᵃ xs Θ) (SDs : ModeCorrectᵃˢ xs Ds) 
      → ModeCorrectᵃˢ xs (Θ ⊢[ Check ] C ∙ Ds)

Synthesis : TExp Ξ → ArgsD Ξ → Set
Synthesis C Ds = ∃[ xs ] (fv C ⊆ xs × ModeCorrectᵃˢ ∅ xs Ds)

Checking : TExp Ξ → ArgsD Ξ → Set
Checking C Ds = ∃[ xs ] ModeCorrectᵃˢ (fv C) xs Ds

ModeCorrect : Desc → Set
ModeCorrect = All λ
  where (ι Check C Ds) → Checking  C Ds
        (ι Infer C Ds) → Synthesis C Ds