{-# OPTIONS --safe #-}

module Prelude.Logic where

open import Prelude.Level
open import Prelude.Equivalence

private variable
  A B C : Set ℓ
  I : Set ℓ
  J : I → Set ℓ
  X Y : (i : I) → J i → Set ℓ

infixr -10 _⇒₁_ _⇒_

Fam₁ : (ℓ : Level) (I : Set ℓ₁) → Set _
Fam₁ ℓ I = (i : I) → Set ℓ

Fam₂ : (ℓ : Level) (I : Set ℓ₁) (J : I → Set ℓ₂) → Set _
Fam₂ ℓ I J = (i : I) → J i → Set ℓ

_⇒₁_ : (X : Fam₁ ℓ₁ I) (Y : Fam₁ ℓ₂ I) → Set _
X ⇒₁ Y = ∀ {i} → X i → Y i

_⇒_ : (X : Fam₂ ℓ I J) (Y : Fam₂ ℓ′ I J) → Set _
X ⇒ Y = ∀ {i j} → X i j → Y i j
