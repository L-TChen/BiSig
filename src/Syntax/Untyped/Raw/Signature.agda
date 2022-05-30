open import Prelude

module Syntax.Untyped.Raw.Signature (Id : Set) where

open import Syntax.Untyped.Signature using (Sig; ∣_∣; sig; arity) public

private
  variable
    O   : Set

_^_ : (X : Set ℓ) → ℕ → Set ℓ
X ^ zero       = ⊤
X ^ suc n      = (X ^ n) × X

⟦_⟧ᶜ_ : (as : List ℕ) (X : Set) → Set
⟦ []     ⟧ᶜ _ = ⊤
⟦ a ∷ as ⟧ᶜ X = ((Id ^ a) × X)  × ⟦ as ⟧ᶜ X

⟦_⟧_ : (s : Sig O) (X : Set) → Set
⟦_⟧_ {O} (sig ar) X = Σ[ o ∈ O ] ⟦ ar o ⟧ᶜ X