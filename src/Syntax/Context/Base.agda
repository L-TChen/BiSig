{-# OPTIONS --safe #-}

open import Prelude

module Syntax.Context.Base where

Context = List

private variable
  T     : Set
  Γ Δ Ξ : Context T
  A B   : T

Ren : (Γ Δ : Context T) → Set
Ren Γ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

ext : Ren Γ Δ
  → Ren (A ∷ Γ) (A ∷ Δ)
ext ρ (here px) = here px
ext ρ (there x) = there (ρ x)

extⁿ : Ren Γ Δ
  → Ren (Ξ ++ Γ) (Ξ ++ Δ)
extⁿ {Ξ = []}    ρ i         = ρ i
extⁿ {Ξ = A ∷ Ξ} ρ (here px) = here px
extⁿ {Ξ = A ∷ Ξ} ρ (there i) = there (extⁿ ρ i)
