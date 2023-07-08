import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Pre.Term {SD : S.Desc} (D : B.Desc SD) where

open import Prelude

open import Syntax.Simple SD

open import Theory.Erasure

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
        Pre Syn (` i)

  _∋_ : (A : Ty)
      → Pre Chk r
      → ---------------
        Pre Syn (A ∋ r)

  _↑  : Pre Syn r
      → ---------
        Pre Chk r

  op  : {rs : R.⟦ erase D ⟧ Raw n}
      → ⟦ D ⟧ Raw Pre d rs
      → --------------------------
        Pre d (op rs)
