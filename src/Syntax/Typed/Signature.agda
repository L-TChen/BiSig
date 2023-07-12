import Syntax.Simple.Signature as S

module Syntax.Typed.Signature (SD : S.SigD)  where

open import Prelude

open import Syntax.Simple SD as Ty

record ArgD (Ξ : ℕ) : Set where
  constructor _⊢_
  field
    cxt  : TExps Ξ -- context extension
    type : TExp  Ξ -- the type of an argument

ArgsD : ℕ → Set
ArgsD Ξ = List (ArgD Ξ)

record OpD : Set where
  constructor ι
  field
    {tvars} : ℕ            -- the number of type variables
    type    : TExp  tvars  -- the target type
    args    : ArgsD tvars  -- the arguments of a typing rule

record SigD : Set₁ where
  constructor sigd
  field
    Op        : Set
    ⦃ decOp ⦄ : DecEq Op
    ar        : Op → OpD

open SigD public

ρ-syntax : ∀ {Ξ} → ArgD Ξ → ArgsD Ξ → ArgsD Ξ
ρ-syntax D Ds = D ∷ Ds

syntax ρ-syntax D Ds = ρ[ D ] Ds
infixr 7 ρ-syntax
infix  7 _⊢_

syntax ι {Ξ} A D = Ξ ▷ D ⦂ A

infix  6 ι
