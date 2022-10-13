open import Prelude

module Theory.Dichotomy.Context (Id : Set) where

open import Syntax.Context.Base         as Nameless
open import Syntax.NamedContext.Base Id as Named

private variable
  T     : Set
  A B C : T
  x y   : Id
  Γ     : Named.Context T

∥_∥ctx : Named.Context T → Nameless.Context T
∥ ∅         ∥ctx = ∅
∥ x ⦂ A , Γ ∥ctx = A ∙ ∥ Γ ∥ctx

∥_∥∈ : x ⦂ A ∈ Γ → A ∈ ∥ Γ ∥ctx
∥ zero     ∥∈ = here refl
∥ suc ¬p x ∥∈ = there ∥ x ∥∈
