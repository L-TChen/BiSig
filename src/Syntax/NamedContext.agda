open import Prelude

module Syntax.NamedContext (Id : Set) where

infixl 5 _⦂_,_
infix  4 _⦂_∈_

-- data Context (T : Set) : Set where
--   ∅     : Context T
--   _⦂_,_ : (x : Id) (A : T) (Γ : Context T) → Context T

Context : (T : Set) → Set
Context T = List (Id × T)

pattern _⦂_,_ x A Γ = (x , A) ∙ Γ

private variable
  T   : Set
  Γ   : Context T
  x y : Id
  A B : T

data _⦂_∈_ {T : Set} (x : Id) (A : T) : Context T → Set where
  zero
    :  x ⦂ A ∈ x ⦂ A , Γ
  suc
    : (¬p : x ≢ y)
    → (i : x ⦂ A ∈ Γ)
    → x ⦂ A ∈ y ⦂ B , Γ

uniq-∈ : x ⦂ A ∈ Γ → x ⦂ B ∈ Γ → A ≡ B
uniq-∈ zero       zero       = refl
uniq-∈ (suc _ i) (suc _ j)   = uniq-∈ i j
uniq-∈ zero       (suc ¬p j) = ⊥-elim₀ (¬p refl)
uniq-∈ (suc ¬p i) zero       = ⊥-elim₀ (¬p refl)

ext∈ : x ≢ y
  → ¬ (∃[ A ] x ⦂ A ∈ Γ)
  → ¬ (∃[ A ] x ⦂ A ∈ y ⦂ B , Γ)
ext∈ ¬p ¬∃ (A , zero)     = ¬p refl
ext∈ ¬p ¬∃ (A , suc ¬q i) = ¬∃ (A , i)
