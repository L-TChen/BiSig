{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Pre.Generalised.Term {SD : S.Desc} (D : B.Desc SD) where

open import Syntax.Simple SD

open import Theory.Erasure.Description

module R where
  open import Syntax.Typed.Raw.Functor (SD)   public
  open import Syntax.Typed.Raw.Term (erase D) public
open R using (Raw; `_; _∋_; op)

open import Syntax.BiTyped.Pre.Generalised.Functor SD

private variable
  v e : Bool
  n   : ℕ
  r   : Raw n
  d   : Mode

infix 5 _∋_

data Tm : (valid exact : Bool) → Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ----------------------
        Tm true true Inf (` i)

  _∋_ : (A : TExp₀)
      → Tm v e    Chk      r
      → ---------------------
        Tm v true Inf (A ∋ r)

  _↑  : Tm v true  Inf r
      → ----------------
        Tm v false Chk r

  ?∋_ : Tm v     true  Chk r
      → --------------------
        Tm false false Inf r

  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → (ts : ⟦ D ⟧ Raw Tm v e d rs)
      → ----------------------------
        Tm v e d (op rs)
