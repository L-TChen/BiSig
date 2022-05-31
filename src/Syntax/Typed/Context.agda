open import Prelude

module Syntax.Typed.Context (T : Set) where

open import Data.List

Ctx = List T

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Ctx → Set ℓ

Fam₀ = Fam lzero

private variable
  Γ   : Ctx
  A B : T

pattern ∅       = []
pattern _∙_ A Γ = A ∷ Γ

infix 4 _∈_
data _∈_ : Fam₀ where
  zero
    : A ∈ A ∙ Γ
  suc
    : A ∈ Γ
    → A ∈ B ∙ Γ