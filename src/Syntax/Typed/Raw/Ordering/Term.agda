{-# OPTIONS --safe #-}

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw.Ordering.Term {SD : S.Desc} (D : T.Desc SD) where

open import Prelude

open import Syntax.Simple            SD
import      Syntax.Typed.Raw.Functor SD as R
open import Syntax.Typed.Raw.Term     D

open import Syntax.Typed.Raw.Ordering.Functor SD

private variable
  n    : ℕ
  r r' : Raw _

data _≤ᴬ_ : Fam₀ Raw where

  `_   : (i : Fin n)
       → --------------
         (` i) ≤ᴬ (` i)

  _∋_  : (τ : Ty)
       → r ≤ᴬ r'
       → -------------------
         (τ ∋ r) ≤ᴬ (τ ∋ r')

  _∋⁺_ : (τ : Ty)
       → r ≤ᴬ r'
       → -------------
         r ≤ᴬ (τ ∋ r')

  op   : {rs rs' : R.⟦ D ⟧ Raw n}
       → ⟦ D ⟧ Raw _≤ᴬ_ rs rs'
       → ------------------------
         op rs ≤ᴬ op rs'
