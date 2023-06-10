{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Pre.Term {SD : S.Desc} (D : B.Desc SD) where

open import Prelude

open import Syntax.Simple SD

open import Theory.Erasure.Description

open import Syntax.Typed.Raw (erase D)

open import Syntax.BiTyped.Pre.Functor SD

private variable
  n : ℕ
  r : Raw n
  d : Mode

infix 5 _∋_

data Pre : Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → -------------
        Pre Inf (` i)

  _∋_ : (A : TExp₀)
      → Pre Chk r
      → ---------------
        Pre Inf (A ∋ r)

  _↑  : Pre Inf r
      → ---------
        Pre Chk r

  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → ⟦ D ⟧ Raw Pre d rs
      → --------------------------
        Pre d (op rs)
