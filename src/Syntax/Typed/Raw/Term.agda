import Syntax.Simple.Signature as S
import Syntax.Typed.Signature  as T

module Syntax.Typed.Raw.Term {SD : S.SigD} (D : T.SigD SD) where

open import Prelude

open import Syntax.Simple SD
open import Syntax.Typed.Raw.Functor SD

open T SD

private variable
  n : ℕ

infix 5 _∋_

data Raw : ℕ → Set where
  `_  : Fin n                → Raw n
  _∋_ : (A : Ty) (t : Raw n) → Raw n
  op  : ⟦ D ⟧ Raw n          → Raw n
