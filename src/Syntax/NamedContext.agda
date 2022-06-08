open import Prelude

module Syntax.NamedContext (Id : Set) where

infixl 5 _,_⦂_
infix  4 _∋_⦂_

data Context (T : Set) : Set where
  ∅     : Context T
  _,_⦂_ : Context T → Id → T → Context T

private variable
  T   : Set
  Γ   : Context T
  x y : Id
  A B : T

data _∋_⦂_ {T : Set}: Context T → Id → T → Set where
  zero
    : Γ , x ⦂ A ∋ x ⦂ A
  suc
    : x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A