open import Prelude

import Syntax.Simple.Description as S

module Syntax.BiTyped.Description {SD : S.Desc} where

open import Syntax.Context
open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)

private variable
  Ξ   : ℕ
  m   : Mode
  B   : TExp Ξ

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
    mode : Mode
    type : TExp vars
    args : ArgsD vars

Desc : Set
Desc = List ConD

ρ-syntax : ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∙ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds

infix  6 ι
_⇉_ _⇇_ : List (TExp Ξ) → (B : TExp Ξ) → ArgD Ξ
Θ ⇉ B = record { cxt = Θ ; mode = Infer ; type = B }
Θ ⇇ B = record { cxt = Θ ; mode = Check ; type = B }

_▷_⇉_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇉ A = ι Infer A D

_▷_⇇_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇇ A = ι Check A D

fvArgD : (D : ArgD Ξ) → List (Fin Ξ)
fvArgD D = fv $ ArgD.type D

modeArgD : ArgD Ξ → Mode
modeArgD D = ArgD.mode D