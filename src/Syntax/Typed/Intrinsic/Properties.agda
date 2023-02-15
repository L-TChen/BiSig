{-# OPTIONS --safe #-} 

open import Prelude
import Syntax.Simple.Description as S
open import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Properties {SD : S.Desc} {D : T.Desc {SD}} where
open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T; Tm to TExp; Tms to TExps; Sub to TSub; _≟_ to _≟T_)

open import Syntax.Context SD

open import Syntax.Typed.Intrinsic.Functor
open import Syntax.Typed.Intrinsic.Term D

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)

private
  variable
    n m   : ℕ
    σ     : TSub n m
    A B   : TExp m
    Γ Δ   : Cxt m

-- rename-id=id : (t : Tm m A Γ) → rename id t ≡ t
-- rename-id=id (` x)  = refl
-- rename-id=id (op (D , D∈Ds , σ , eq , ts)) =  cong op {!!}   

