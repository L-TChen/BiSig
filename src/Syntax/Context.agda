open import Prelude

module Syntax.Context (T : Set) where

open import Data.List

Ctx = List T

pattern ∅       = []
pattern _∙_ A Γ = A ∷ Γ

data _∈_ (A : T) : Ctx → Set where
  zero : ∀ {Γ}
    → A ∈ (A ∙ Γ)
  suc  : ∀ {Γ B}
    → A ∈ Γ
    → A ∈ (B ∙ Γ)