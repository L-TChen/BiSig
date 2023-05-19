{-# OPTIONS --safe #-}

open import Prelude

module Theory.Ontologisation.Context (Id : Set) where

open import Syntax.Context.Base         as Nameless
open import Syntax.NamedContext.Base Id as Named

private variable
  T     : Set
  A B C : T
  x y   : Id
  Γ     : Named.Context T

∥_∥cxt : Named.Context T → Nameless.Context T
∥ []        ∥cxt = []
∥ x ⦂ A , Γ ∥cxt = A ∷ ∥ Γ ∥cxt

∥_∥∈ : x ⦂ A ∈ Γ → A ∈ ∥ Γ ∥cxt
∥ zero     ∥∈ = here refl
∥ suc ¬p x ∥∈ = there ∥ x ∥∈
