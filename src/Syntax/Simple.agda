{-# OPTIONS --safe #-}

import Syntax.Simple.Description as S

module Syntax.Simple (SD : S.Desc) where

open import Syntax.Simple.Term                   SD public
  renaming (Tm to TExp; Tm₀ to TExp₀; Tms to TExps; Tms₀ to TExps₀;
            Sub to TSub; Ren to TRen)
open import Syntax.Simple.Properties             SD public
open import Syntax.Simple.Association            SD public
open import Syntax.Simple.Unification            SD public
open import Syntax.Simple.Unification.Properties SD public
