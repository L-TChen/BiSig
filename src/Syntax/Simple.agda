import Syntax.Simple.Description as S

module Syntax.Simple (SD : S.Desc) where

open import Syntax.Simple.Term                   SD public
  renaming (Tm to TExp; Tm₀ to Ty; Tms to TExps
    ; Sub to TSub; Ren to TRen)
open import Syntax.Simple.Properties             SD public
