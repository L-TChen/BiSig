{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Intrinsic.Term {SD : S.Desc} (D : B.Desc SD) where

open import Syntax.Simple SD

open import Syntax.BiTyped.Raw.Intrinsic.Functor SD

open B SD

private variable
  n    : ℕ
  mode : Mode

infix 5 _∋_

data Raw : ℕ → Mode → Set where
  `_  : Fin n                       → Raw n Inf
  _∋_ : (A : TExp₀) (t : Raw n Chk) → Raw n Inf
  _↑  : (t : Raw n Inf)             → Raw n Chk
  op  : ⟦ D ⟧ Raw n mode            → Raw n mode

Raw⇐ Raw⇒ : ℕ → Set
Raw⇐ n = Raw n Chk
Raw⇒ n = Raw n Inf
