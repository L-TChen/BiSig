{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Association (D : Desc) where

open import Syntax.Simple.Term D

private variable
  n m l : ℕ
  
data AList : (m n : ℕ) → Set where
  []    : AList n n
  _/_∷_ : (t : Tm m) (x : Fin (suc m)) (σ : AList m n) → AList (suc m) n

_/_∷′_ : Tm m → Fin (suc m) → ∃ (AList m) → ∃ (AList (suc m))
t / x ∷′ (n , σ) = n , (t / x ∷ σ)

_++_ : AList m n → AList n l → AList m l
[]           ++ σ₂ = σ₂
(t / x ∷ σ₁) ++ σ₂ = t / x ∷ (σ₁ ++ σ₂)

toSub : AList m n → Sub m n
toSub []          = ids
toSub (t / x ∷ ρ) = (t for x) ⨟ toSub ρ

infixl 8 _⟪_⟫ₐ _⟪_⟫ₐₛ

_⟪_⟫ₐ : Tm m → AList m n → Tm n
t ⟪ σ ⟫ₐ = t ⟪ toSub σ ⟫

_⟪_⟫ₐₛ : Tm m ^ l → AList m n → Tm n ^ l
ts ⟪ σ ⟫ₐₛ = subⁿ (toSub σ) ts
