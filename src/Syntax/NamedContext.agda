{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.NamedContext (D : Desc) (Id : Set) where

open import Syntax.NamedContext.Base Id public
open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D

Cxt : ℕ → Set
Cxt m = Context (Tm m)

cxtSub : {m n : ℕ} → Sub m n
  → Cxt m → Cxt n
cxtSub σ []       = []
cxtSub σ ((x , A) ∷ Γ) = (x , sub σ A) ∷ cxtSub σ Γ

instance
  CxtSubIsPresheaf : IsPresheaf Cxt
  CxtSubIsPresheaf ._⟨_⟩ Γ σ = cxtSub σ Γ

  CxtAListIsPresheaf : IsPresheaf Cxt
  CxtAListIsPresheaf ._⟨_⟩ Γ σ = Γ ⟨ toSub σ ⟩
