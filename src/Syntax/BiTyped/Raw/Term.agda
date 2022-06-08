open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc} (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.BiTyped.Raw.Description

private variable
  Ξ   : ℕ
  m   : Mode

data Raw (Id : Set) : Mode → Set where
  `_  : (x : Id)                   → Raw Id Infer
  _⦂_ : (t : Raw Id Check) (A : T) → Raw Id Infer
  _↑  : (t : Raw Id Infer)         → Raw Id Check
  op  : (⟦ D ⟧ Raw) Id m           → Raw Id m