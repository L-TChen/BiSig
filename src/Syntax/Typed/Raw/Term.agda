{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw.Term {SD : S.Desc} (D : T.Desc SD) where

open import Syntax.Simple SD
open import Syntax.Typed.Raw.Functor SD

open T SD

private variable
  n : ℕ

infix 5 _∋_

data Raw : ℕ → Set where
  `_  : Fin n                   → Raw n
  _∋_ : (A : TExp₀) (t : Raw n) → Raw n
  op  : ⟦ D ⟧ Raw n             → Raw n
