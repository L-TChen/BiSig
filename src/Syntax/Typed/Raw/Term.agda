{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Raw.Term {SD : S.Desc} (Id : Set) (D : T.Desc SD) where

open import Syntax.Simple SD
open import Syntax.Typed.Raw.Functor SD Id

open T SD

private variable
  n m k l : ℕ
  Θ Θ₁ Θ₂ : ℕ

infix 4 _⦂_

data Raw (Θ : ℕ) : Set where
  `_  : (x : Id)                 → Raw Θ
  _⦂_ : (t : Raw Θ) (A : TExp Θ) → Raw Θ
  op  : ⟦ D ⟧ (Raw Θ)            → Raw Θ

module _ (ρ : Ren Θ₁ Θ₂) where mutual
  trename : Raw Θ₁ → Raw Θ₂
  trename (` x)         = ` x
  trename (t ⦂ A)       = trename t ⦂ rename ρ A
  trename (op (i , ts)) = op (i , trenameⁿ ts)

  trenameⁿ : {AD : ArgsD k}
    → ⟦ AD ⟧ᵃˢ (Raw Θ₁) → ⟦ AD ⟧ᵃˢ (Raw Θ₂)
  trenameⁿ {AD = []}     _       = _
  trenameⁿ {AD = A ∷ D} (t , ts) = trenameᵃ t , trenameⁿ ts

  trenameᵃ : {Δ : TExps k}
    → ⟦ Δ ⟧ᵃ (Raw Θ₁) → ⟦ Δ ⟧ᵃ (Raw Θ₂)
  trenameᵃ {Δ = []}    t       = trename t
  trenameᵃ {Δ = A ∷ Δ} (x , t) = x , trenameᵃ t
