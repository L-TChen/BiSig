open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description {SD : S.Desc} where

open import Syntax.Context
open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)

private variable
  Ξ   : ℕ

infixr 5 ⇉_ ⇇_
infix  6 _▷_⇉_ _▷_⇇_
infixr 7 ρ-syntax 

data ArgD  (Ξ : ℕ) : Set where
  ι   : (m : Mode)   (B : TExp Ξ) → ArgD Ξ
  _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

ArgsD : ℕ → Set
ArgsD Ξ = List (ArgD Ξ)

record ConD : Set where
  constructor ι
  field
    vars : ℕ
    mode : Mode
    type : TExp vars
    args : ArgsD vars

Desc : Set
Desc = List ConD

ρ-syntax : ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∙ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds

⇉_ ⇇_ : TExp Ξ → ArgD Ξ
⇉_ = ι Infer
⇇_ = ι Check

_▷_⇉_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇉ A = ι Ξ Infer A D

_▷_⇇_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇇ A = ι Ξ Check A D

fvArgD : ArgD Ξ → List (Fin Ξ)
fvArgD (ι m B) = fv B
fvArgD (A ∙ D) = fvArgD D

modeArgD : ArgD Ξ → Mode
modeArgD (ι m _) = m
modeArgD (_ ∙ D) = modeArgD D