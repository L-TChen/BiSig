import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

module Syntax.BiTyped.Pre.Generalised.Term {SD : S.SigD} (D : B.SigD SD) where

open import Prelude

open import Syntax.Simple SD

open import Theory.Erasure

open import Syntax.Typed.Raw (erase D)

open import Syntax.BiTyped.Pre.Generalised.Functor SD

private variable
  v e : Bool
  n   : ℕ
  r   : Raw n
  d   : Mode

infix 5 _∋_

data Pre? : (valid exact : Bool) → Mode → {n : ℕ} → Raw n → Set where

  `_  : (i : Fin n)
      → ------------------------
        Pre? true true Syn (` i)

  _∋_ : (A : Ty)
      → Pre? v e    Chk      r
      → -----------------------
        Pre? v true Syn (A ∋ r)

  _↑  : Pre? v true  Syn r
      → ------------------
        Pre? v false Chk r

  ?∋_ : Pre? v     true  Chk r
      → ----------------------
        Pre? false false Syn r

  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → ⟦ D ⟧ Raw Pre? v e d rs
      → --------------------------
        Pre? v e d (op rs)
