{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description (SD : S.Desc) where

open import Syntax.Context
open import Syntax.Simple.Term SD as Ty
  renaming (Tm to TExp)

private variable
  Ξ : ℕ
  d : Mode
  B : TExp Ξ

infix  6 _▷_⇒_ _▷_⇐_
infixr 7 ρ-syntax _⊢[_]_

record ArgD (Ξ : ℕ) : Set where
  constructor _⊢[_]_
  field
    cxt  : List (TExp Ξ)
    mode : Mode
    type : TExp Ξ

ArgsD : ℕ → Set
ArgsD Ξ = List (ArgD Ξ)

record ConD : Set where
  constructor ι
  field
    {vars} : ℕ
    mode   : Mode
    type   : TExp  vars
    args   : ArgsD vars

record Desc : Set₁ where
  constructor desc
  field
    Op        : Set
    ⦃ decOp ⦄ : DecEq Op
    rules     : Op → ConD

open Desc public

ρ-syntax : ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∷ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds

infix  6 ι

_▷_⇒_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇒ A = ι Inf A D

_▷_⇐_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇐ A = ι Chk A D

modeArgD : ArgD Ξ → Mode
modeArgD D = ArgD.mode D
