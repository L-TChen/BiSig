import Syntax.Simple.Signature as S

module Theory.ModeCorrectness.Decidability (SD : S.SigD) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.BiTyped.Signature SD

open import Theory.ModeCorrectness.Signature SD

private variable
  Ξ : ℕ

