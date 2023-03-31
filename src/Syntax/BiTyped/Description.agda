{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description {SD : S.Desc} where

open import Syntax.Context
open import Syntax.Simple.Term SD as Ty
  renaming (Tm to TExp)

private variable
  n m : ℕ
  mod : Mode
  B   : TExp n

infixr 4 _⇉_ _⇇_
infix  6 _▷_⇉_ _▷_⇇_
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
    type   : TExp vars
    args   : ArgsD vars

Desc : Set
Desc = List ConD

ρ-syntax : ArgD n → ArgsD n → ArgsD n
ρ-syntax D Ds = D ∙ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds

infix  6 ι
_⇉_ _⇇_ : List (TExp n) → (B : TExp n) → ArgD n
Θ ⇉ B = record { cxt = Θ ; mode = Infer ; type = B }
Θ ⇇ B = record { cxt = Θ ; mode = Check ; type = B }

_▷_⇉_ : (n : ℕ) (D : ArgsD n) (A : TExp n) → ConD
Ξ ▷ D ⇉ A = ι Infer A D

_▷_⇇_ : (n : ℕ) (D : ArgsD n) (A : TExp n) → ConD
Ξ ▷ D ⇇ A = ι Check A D

-- fvArgD : (D : ArgD n) → List (Fin n)
-- fvArgD D = fv $ ArgD.type D

modeArgD : ArgD n → Mode
modeArgD D = ArgD.mode D
