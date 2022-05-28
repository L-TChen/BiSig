open import Prelude
open import Syntax.Untyped.Signature using (Sig)

module Syntax.Untyped.Raw.Term (Id : Set) {O : Set} (s : Sig O) where

open import Syntax.Untyped.Raw.Signature Id

data Raw : Set where
  `_ : Id        → Raw
  op : ⟦ s ⟧ Raw → Raw
