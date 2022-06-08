open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc} (D : B.Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.BiTyped.Raw.Functor {SD} Id

private variable
  Ξ   : ℕ
  m   : Mode

data Raw : Mode → Set where
  `_  : (x : Id)                → Raw Infer
  _∈_ : (t : Raw Check) (A : T) → Raw Infer
  _↑  : (t : Raw Infer)         → Raw Check
  op  : (⟦ D ⟧ Raw) m           → Raw m