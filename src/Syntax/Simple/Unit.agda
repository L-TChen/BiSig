open import Prelude

module Syntax.Simple.Unit where

open import Syntax.Simple.Description
open import Syntax.Simple.Term

⋆D : Desc
⋆D = 0 ∙ ∅

⋆T = Tm₀ ⋆D

⋆ : {Ξ : ℕ} → Tm ⋆D Ξ
⋆ = op (inl tt)