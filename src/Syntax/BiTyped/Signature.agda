{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Signature as S

module Syntax.BiTyped.Signature (SD : S.SigD) where

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

ArgsD = List ∘ ArgD

record OpD : Set where
  constructor ι
  field
    {tvars} : ℕ
    mode    : Mode
    type    : TExp  tvars
    args    : ArgsD tvars
open OpD public

record SigD : Set₁ where
  constructor sigd
  field
    Op        : Set
    ⦃ decOp ⦄ : DecEq Op
    ar        : Op → OpD

open SigD public

ρ-syntax : ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∷ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds

infix  6 ι

_▷_⇒_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → OpD
Ξ ▷ D ⇒ A = ι Syn A D

_▷_⇐_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → OpD
Ξ ▷ D ⇐ A = ι Chk A D

modeArgD : ArgD Ξ → Mode
modeArgD D = ArgD.mode D
