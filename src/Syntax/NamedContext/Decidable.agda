open import Prelude

module Syntax.NamedContext.Decidable {Id : Set} (_≟_ : (x y : Id) → Dec (x ≡ y)) where

open import Syntax.NamedContext Id

private variable
  T : Set ℓ

lookup : (Γ : Context T) (x : Id)
  → Dec (∃[ A ] x ⦂ A ∈ Γ)
lookup ∅           x = no λ ()
lookup (y ⦂ B , Γ) x with x ≟ y
... | yes refl = yes (B , zero)
... | no ¬p    with lookup Γ x
...            | no ¬q = no (ext∈ ¬p ¬q)
...            | yes (A , i) = yes (A , suc ¬p i)