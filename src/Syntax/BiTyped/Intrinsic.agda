{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as T

module Syntax.BiTyped.Intrinsic {SD : S.Desc} (D : T.Desc SD) where

open import Syntax.BiTyped.Intrinsic.Functor SD   public
open import Syntax.BiTyped.Intrinsic.Term       D public
