open import Prelude

module Syntax.Context where

Ctx = List

private variable
  T   : Set
  Γ Δ : Ctx T
  A B : T

Ren : (Γ Δ : Ctx T) → Set
Ren Γ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

ext : Ren Γ Δ
  → Ren (A ∙ Γ) (A ∙ Δ)
ext ρ (here px) = here px
ext ρ (there x) = there (ρ x)