open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.RawNoMode.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.BiTyped.RawNoMode.Functor {SD} Id

private variable
  Ξ   : ℕ
  m   : Mode

infix 4 _⦂_

data Raw : Fam₀ where
  `_  : (x : Id)          → Raw
  _⦂_ : (t : Raw) (A : T) → Raw
  op  : ⟦ D ⟧ Raw         → Raw
