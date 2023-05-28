{-# OPTIONS --with-K --safe #-}

open import Prelude

module Syntax.NamedContext.Base (Id : Set) where

infixl 6 _⦂_,_
infix  5 _⦂_∈_

Context : (T : Set) → Set
Context T = List (Id × T)

pattern _⦂_,_ x A Γ = (x , A) ∷ Γ

private variable
  T   : Set
  Γ   : Context T
  x y : Id
  A B : T

data _⦂_∈_ {T : Set} (x : Id) (A : T) : Context T → Set where
  zero
    : x ⦂ A ∈ x ⦂ A , Γ
  suc
    : (¬p : x ≢ y)
    → (i : x ⦂ A ∈ Γ)
    → x ⦂ A ∈ y ⦂ B , Γ
    
-- Only needed without K
-- uniq-∈₀ : x ⦂ B ∈ y ⦂ A , Γ → x ≡ y → A ≡ B
-- uniq-∈₀ zero       p = refl
-- uniq-∈₀ (suc ¬p x) p = ⊥-elim₀ (¬p p)

uniq-∈ : x ⦂ A ∈ Γ → x ⦂ B ∈ Γ → A ≡ B
-- uniq-∈ zero       y             = uniq-∈₀ y refl
-- uniq-∈ (suc ¬p _) zero          = ⊥-elim₀ (¬p refl)
-- uniq-∈ (suc ¬p x∈) (suc ¬p₁ y∈) = uniq-∈ x∈ y∈

-- If `--with-K` is turned on, then the following definition suffices.
uniq-∈ (zero ) (zero ) = refl
uniq-∈ (suc _ i)   (suc _ j)   = uniq-∈ i j
uniq-∈ (zero ) (suc ¬p j)  = ⊥-elim₀ (¬p refl)
uniq-∈ (suc ¬p i)  (zero ) = ⊥-elim₀ (¬p refl)

ext∈ : x ≢ y
  → ¬ (∃[ A ] x ⦂ A ∈ Γ)
  → ¬ (∃[ A ] x ⦂ A ∈ y ⦂ B , Γ)
ext∈ ¬p ¬∃ (A , zero )     = ¬p refl
ext∈ ¬p ¬∃ (A , suc ¬q i) = ¬∃ (A , i)
