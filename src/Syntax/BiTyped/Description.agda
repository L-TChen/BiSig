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
infixr 7 ρ 
syntax ρ D Ds      = ρ[ D ] Ds

data ArgD  (Ξ : ℕ) : Set where
  ι   : (m : Mode)   (B : TExp Ξ) → ArgD Ξ
  _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

data ArgsD (Ξ : ℕ) : Set where
  ι :                               ArgsD Ξ
  ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

record ConD : Set where
  constructor ι
  field
    vars : ℕ
    mode : Mode
    type : TExp vars
    args : ArgsD vars

Desc : Set
Desc = List ConD

⇉_ ⇇_ : TExp Ξ → ArgD Ξ
⇉_ = ι Infer
⇇_ = ι Check

_▷_⇉_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇉ A = ι Ξ Infer A D

_▷_⇇_ : (Ξ : ℕ) (D : ArgsD Ξ) (A : TExp Ξ) → ConD
Ξ ▷ D ⇇ A = ι Ξ Check A D