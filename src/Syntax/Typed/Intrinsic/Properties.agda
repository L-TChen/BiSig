{-# OPTIONS --safe #-}

open import Prelude
import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Properties {SD : S.Desc} {D : T.Desc SD} where
open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T; Tm to TExp; Tms to TExps; Sub to TSub)

open import Syntax.Context SD

open import Syntax.Typed.Intrinsic.Functor
open import Syntax.Typed.Intrinsic.Term D

private
  variable
    n m   : ℕ
    σ     : TSub n m
    A B   : TExp m
    Γ Δ   : Cxt m

-- rename-id=id : (t : Tm m A Γ) → rename id t ≡ t
-- rename-id=id (` x)  = refl
-- rename-id=id (op (i , σ , eq , ts)) =  cong op {!!}
