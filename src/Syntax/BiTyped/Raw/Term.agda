open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp)

open import Syntax.BiTyped.Raw.Functor {SD} Id

private variable
  n m k : ℕ
  mod : Mode

infix 4 _⦂_

data Raw (m : ℕ) : Mode → Set where
  `_  : (x : Id)                       → Raw m Infer
  _⦂_ : (t : Raw m Check) (A : TExp m) → Raw m Infer
  _↑  : (t : Raw m Infer)              → Raw m Check
  op  : (⟦ D ⟧ Raw m) mod              → Raw m mod

Raw⇇ Raw⇉ : ℕ → Set
Raw⇇ m = Raw m Check
Raw⇉ m = Raw m Infer

mutual
  twk : m ≤ n → Raw m mod → Raw n mod
  twk le (` x)   = ` x
  twk le (t ⦂ A) = twk le t ⦂ wk le A
  twk le (t ↑)   = twk le t ↑
  twk le (op (D , i , refl , ts)) = op (D , i , refl , twkⁿ le ts)

  twkⁿ : {D : B.ArgsD k}
    → m ≤ n → ⟦ D ⟧ᵃˢ Raw m → ⟦ D ⟧ᵃˢ Raw n
  twkⁿ {D = ∅}     le (lift _) = _
  twkⁿ {D = A ∙ D} le (t , ts) = twkᵃ le t , twkⁿ le ts

  twkᵃ : {D : List (TExp k)}
    → m ≤ n → ⟦ D ⟧ᵃ Raw m mod → ⟦ D ⟧ᵃ Raw n mod
  twkᵃ {D = ∅}     le t       = twk le t
  twkᵃ {D = A ∙ D} le (x , t) = x , twkᵃ le t
