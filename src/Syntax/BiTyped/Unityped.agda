open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Unityped (D : B.Desc {S.⋆D}) where

open import Syntax.BiTyped.Term {S.⋆D} D public