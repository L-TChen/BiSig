open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Description {SD : S.Desc}  where

open import Syntax.Simple.Term SD as Ty
  renaming (Tm to TExp)
open import Syntax.Context

record ArgD (Ξ : ℕ) : Set where
  constructor _⊢_
  field
    cxt  : List (TExp Ξ)
    type : TExp Ξ

ArgsD : ℕ → Set
ArgsD Ξ = List (ArgD Ξ)

record ConD : Set where
  constructor ι
  field
    {vars} : ℕ
    type   : TExp  vars
    args   : ArgsD vars

Desc : Set
Desc = List ConD

ρ-syntax : ∀ {Ξ} → ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∙ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds
infixr 7 ρ-syntax
infix  7 _⊢_

syntax ι {Ξ} A D = Ξ ▷ D ⦂ A

infix  6 ι
