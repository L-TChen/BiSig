{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Association (D : Desc) where

import Data.Fin            as F
import Data.Vec            as V
import Data.Vec.Properties as V

open import Syntax.Simple.Term D
  renaming (_≟_ to _≟Tm_)

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

infixl 8 _⟪_⟫ₐ

_⟪_⟫ₐ : Tm m → AList m n → Tm n
t ⟪ σ ⟫ₐ = t ⟪ toSub σ ⟫

AList→≥ : AList m n → n ≤ m
AList→≥ []           = ≤-refl
AList→≥ (t / x ∷ ge) = ≤-step (AList→≥ ge)

toSub-⨟
  : (ρ : AList m n) (σ : AList n l) 
  → (t : Tm m)
  → t ⟪ ρ ++ σ ⟫ₐ ≡ t ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
toSub-⨟ []          σ t = cong _⟪ σ ⟫ₐ (sym $ sub-id t)
toSub-⨟ (u / x ∷ ρ) σ t = begin
  t ⟪ (u for x) ⨟ toSub (ρ ++ σ) ⟫
    ≡⟨ sub-assoc (u for x) (toSub (ρ ++ σ)) t ⟩
  t ⟪ u for x ⟫ ⟪ ρ ++ σ ⟫ₐ
    ≡⟨ toSub-⨟ ρ σ (t ⟪ u for x ⟫) ⟩
  t ⟪ u for x ⟫ ⟪ ρ ⟫ₐ ⟪ σ ⟫ₐ
    ≡⟨ cong (_⟪ σ ⟫ₐ) (sym $ sub-assoc (u for x) (toSub ρ) t) ⟩
  t ⟪ toSub (u / x ∷ ρ ) ⟫ ⟪ σ ⟫ₐ
    ∎
  where open ≡-Reasoning

toSub-/∷[]
  : {u : Tm m} (x : Fin (suc m))
  → (t : Tm (suc m))
  → t ⟪ u / x ∷ [] ⟫ₐ ≡ t ⟪ u for x ⟫
toSub-/∷[] {_} {u} x t = begin
  t ⟪ u / x ∷ [] ⟫ₐ
    ≡⟨ sub-assoc (u for x) ids t ⟩
  t ⟪ u for x ⟫ ⟪ ids ⟫
    ≡⟨ sub-id _ ⟩
  t ⟪ u for x ⟫
    ∎
  where open ≡-Reasoning
