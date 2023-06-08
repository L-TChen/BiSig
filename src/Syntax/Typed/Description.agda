open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Description (SD : S.Desc)  where

open import Syntax.Simple SD as Ty

record ArgD (Ξ : ℕ) : Set where
  constructor _⊢_
  field
    cxt  : TExps Ξ -- context extension
    type : TExp  Ξ -- the type of an argument

ArgsD : ℕ → Set
ArgsD Ξ = List (ArgD Ξ)

record ConD : Set where
  constructor ι
  field
    {vars} : ℕ           -- the number of type variables
    type   : TExp  vars  -- the target type
    args   : ArgsD vars  -- the arguments of a typing rule

record Desc : Set₁ where
  constructor desc
  field
    Op        : Set
    ⦃ decOp ⦄ : DecEq Op
    rules     : Op → ConD

open Desc public

ρ-syntax : ∀ {Ξ} → ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∷ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds
infixr 7 ρ-syntax
infix  7 _⊢_

syntax ι {Ξ} A D = Ξ ▷ D ⦂ A

infix  6 ι
