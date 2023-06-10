{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Pre.Term {SD : S.Desc} (D : B.Desc SD) where

open import Syntax.Simple SD

open import Theory.Erasure.Description

module R where
  open import Syntax.Typed.Raw.Functor (SD)   public
  open import Syntax.Typed.Raw.Term (erase D) public
open R using (Raw; `_; _∋_; op)

open import Syntax.BiTyped.Pre.Functor SD

private variable
  n : ℕ
  r : Raw n
  d : Mode

infix 5 _∋_

data Tm : Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ------------
        Tm Inf (` i)

  _∋_ : (A : TExp₀)
        (t : Tm Chk r)
      → --------------
        Tm Inf (A ∋ r)

  _↑  : (t : Tm Inf r)
      → --------------
        Tm Chk r

  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → (ts : ⟦ D ⟧ Raw Tm d rs)
      → --------------------------
        Tm d (op rs)
