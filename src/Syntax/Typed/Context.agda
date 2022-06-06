open import Prelude

module Syntax.Typed.Context (T : Set) where

open import Data.List

Ctx = List T

Fam : (ℓ : Level) → Set (lsuc ℓ)
Fam ℓ = T → Ctx → Set ℓ

Fam₀ = Fam lzero

private variable
  Γ   : Ctx
  A B : T

infixr 5 _∙_
pattern ∅       = []
pattern _∙_ A Γ = A ∷ Γ

_≟_ : ∀ {Γ} → (x y : A ∈ Γ) → Dec (x ≡ y)
zero  ≟ zero  = yes refl
suc x ≟ suc y with x ≟ y
... | no ¬p = no λ where refl → ¬p refl
... | yes p = yes (cong suc p)
zero  ≟ suc _ = no λ ()
suc _ ≟ zero  = no λ ()
