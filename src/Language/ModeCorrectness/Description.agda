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

data Synthesisᵃˢ {Ξ : ℕ} : List (Fin Ξ) → ArgsD Ξ → Set where
  nil
    : Synthesisᵃˢ ∅ ∅
  cons⇉
    : (Θ : TExps Ξ) (C : TExp Ξ) (Ds : ArgsD Ξ)
    → (SD : ModeCorrectᵃ xs Θ) (SDs : Synthesisᵃˢ xs Ds) 
    → Synthesisᵃˢ (fv C ++ xs) (Θ ⊢[ Infer ] C ∙ Ds)
  cons⇇
    : (Θ : TExps Ξ) (C : TExp Ξ) (fvD⊆xs : fv C ⊆ xs) (Ds : ArgsD Ξ)
    → (SD : ModeCorrectᵃ xs Θ) (SDs : Synthesisᵃˢ xs Ds) 
    → Synthesisᵃˢ xs (Θ ⊢[ Check ] C ∙ Ds)

Synthesis : (C : TExp Ξ) (Ds : ArgsD Ξ) → Set
Synthesis C Ds = ∃[ xs ] (fv C ⊆ xs × Synthesisᵃˢ xs Ds)

ModeCorrect : ConD → Set
ModeCorrect (ι Infer C Ds) = Synthesis C Ds
ModeCorrect (ι Check C Ds) = ⊤

AllModeCorrect : Desc → Set
AllModeCorrect = All ModeCorrect