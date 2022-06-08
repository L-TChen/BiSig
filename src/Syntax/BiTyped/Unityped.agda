open import Prelude

open import Syntax.Simple.Unit
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Unityped (D : B.Desc {⋆D}) where

open import Syntax.BiTyped.Term {⋆D} D public