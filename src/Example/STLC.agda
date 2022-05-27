open import Prelude

module Example.STLC where

data Ty : Set where
  ι   : Ty
  _→̇_ : Ty → Ty → Ty
  
open import SOAS.Syntax.Signature Ty
open import SOAS.Syntax.Build     Ty

data Λₒ : Set where
  appₒ lamₒ : {A B : Ty} → Λₒ
  
STLC∶Sig : Signature Λₒ
STLC∶Sig = sig λ where
  (appₒ {A} {B}) → ⊢₀ A →̇ B  , ⊢₀ A ⟼₂ B
  (lamₒ {A} {B}) → A ⊢₁ B      ⟼₁ (A →̇ B)
