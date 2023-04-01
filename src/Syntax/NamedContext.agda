{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.NamedContext (D : Desc) (Id : Set) where

open import Syntax.NamedContext.Base Id public
open import Syntax.Simple.Term       D

Cxt : ℕ → Set
Cxt m = Context (Tm m)

cxtSub : {m n : ℕ} → Sub m n
  → Cxt m → Cxt n
cxtSub σ []       = []
cxtSub σ ((x , A) ∷ Γ) = (x , sub σ A) ∷ cxtSub σ Γ

⟪_⟫cxt = cxtSub

{-# DISPLAY cxtSub σ Γ = ⟪ σ ⟫cxt Γ #-}
