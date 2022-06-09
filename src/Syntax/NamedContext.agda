open import Prelude

module Syntax.NamedContext (Id : Set) where

infixl 5 _⦂_,_
infix  4 _⦂_∈_

data Context (T : Set) : Set where
  ∅     : Context T
  _⦂_,_ : (x : Id) (A : T) (Γ : Context T) → Context T

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
uniq-∈ zero       (suc ¬p j) = ⊥-elim₀ (¬p refl)
uniq-∈ (suc ¬p i) zero       = ⊥-elim₀ (¬p refl)
uniq-∈ (suc _ i) (suc _ j)   = uniq-∈ i j
 
ext∈ : x ≢ y
  → ¬ (∃[ A ] x ⦂ A ∈ Γ)
  → ¬ (∃[ A ] x ⦂ A ∈ y ⦂ B , Γ)
ext∈ ¬p ¬∃ (A , zero)     = ¬p refl
ext∈ ¬p ¬∃ (A , suc ¬q i) = ¬∃ (A , i)

module _ (_≟_ : (x y : Id) → Dec (x ≡ y)) where
  lookup : (Γ : Context T) (x : Id)
    → Dec (∃[ A ] x ⦂ A ∈ Γ)
  lookup ∅           x = no λ ()
  lookup (y ⦂ B , Γ) x with x ≟ y
  ... | yes refl = yes (B , zero)
  ... | no ¬p    with lookup Γ x
  ...            | no ¬q = no (ext∈ ¬p ¬q)
  ...            | yes (A , i) = yes (A , suc ¬p i)