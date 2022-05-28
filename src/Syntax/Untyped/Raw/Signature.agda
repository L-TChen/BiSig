open import Prelude

module Syntax.Untyped.Raw.Signature (Id : Set) where

open import Syntax.Untyped.Signature using (Sig; ∣_∣; sig; arity) public

private
  variable
    O   : Set

⟦_⟧ᵇ_ : (a : ℕ) → (X : Set) → Set
⟦ zero ⟧ᵇ  X = X
⟦ suc a ⟧ᵇ X = Id × ⟦ a ⟧ᵇ X

⟦_⟧ᶜ_ : (as : List ℕ) (X : Set) → Set
⟦ []     ⟧ᶜ _ = ⊤
⟦ a ∷ as ⟧ᶜ X = ⟦ a ⟧ᵇ X × ⟦ as ⟧ᶜ X

⟦_⟧_ : (s : Sig O) (X : Set) → Set
⟦_⟧_ {O} (sig ar) X = Σ[ o ∈ O ] ⟦ ar o ⟧ᶜ X