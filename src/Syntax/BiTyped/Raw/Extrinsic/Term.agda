{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Extrinsic.Term {SD : S.Desc} (D : B.Desc SD) where

open import Syntax.Simple SD

open import Theory.Erasure.Description

module R where
  open import Syntax.Typed.Raw.Functor (SD)   public
  open import Syntax.Typed.Raw.Term (erase D) public
open R using (Raw; `_; _∋_; op)

open import Syntax.BiTyped.Raw.Extrinsic.Functor SD

private variable
  n    : ℕ
  r    : Raw n
  mode : Mode

infix 5 _∋_

data HasMode : {n : ℕ} → Mode → Raw n → Set where
  `_  : (i : Fin n)                     → HasMode Inf (` i)
  _∋_ : (A : TExp₀) (t : HasMode Chk r) → HasMode Inf (A ∋ r)
  _↑  : (t : HasMode Inf r)             → HasMode Chk r
  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → ⟦ D ⟧ (λ k → HasMode {k}) n mode rs
      → HasMode mode (op rs)
