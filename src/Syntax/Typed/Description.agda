open import Prelude

import Syntax.Simple.Description as S

module Syntax.Typed.Description {SD : S.Desc}  where

open import Syntax.Simple.Term SD as Ty
  renaming (Tm₀ to T; Tm to TExp)
open import Syntax.Simple.Operation {SD}
open import Syntax.Context

data ArgD  (Ξ : ℕ) : Set where
  ⊢_  : (B : TExp Ξ)              → ArgD Ξ
  _∙_ : (A : TExp Ξ) (Δ : ArgD Ξ) → ArgD Ξ

data ArgsD (Ξ : ℕ) : Set where
  ι :                               ArgsD Ξ
  ρ : (D : ArgD Ξ) (Ds : ArgsD Ξ) → ArgsD Ξ

data ConD : Set where
  ι : (Ξ : ℕ) (A : TExp Ξ) (D : ArgsD Ξ) → ConD

infix  5 ⊢_
infixr 7 ρ 
syntax ι Ξ A D     = Ξ ▷ D ⦂ A
syntax ρ D Ds      = ρ[ D ] Ds

Desc : Set
Desc = List ConD