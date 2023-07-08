module Prelude.Level where

open import Level                                 public
  using (Level; Lift; lift; 0ℓ; _⊔_)
  renaming (suc to lsuc)

variable
  ℓ ℓ₀ ℓ₁ ℓ₂ ℓ′ ℓ′′ : Level
