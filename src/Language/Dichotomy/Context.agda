open import Prelude

module Language.Dichotomy.Context (Id : Set) where

open import Syntax.Context
open import Syntax.NamedContext Id

private variable
  T     : Set
  A B C : T
  x y   : Id
  Γ     : Context T

∥_∥ctx : Context T → Ctx T
∥ ∅         ∥ctx = ∅
∥ x ⦂ A , Γ ∥ctx = A ∙ ∥ Γ ∥ctx

∥_∥∈ : x ⦂ A ∈ Γ → A ∈ ∥ Γ ∥ctx
∥ zero     ∥∈ = here refl
∥ suc ¬p x ∥∈ = there ∥ x ∥∈