{-# OPTIONS --safe #-}

module Prelude.DecEq where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
  using (Dec; yes; no; _because_; ¬_; ¬?)

record DecEq {a} (A : Set a) : Set a where
  infix 4 _≟_ _≠?_
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  _≠?_ : (x y : A) → Dec (x ≢ y)
  x ≠? y = ¬? (x ≟ y)

open DecEq ⦃...⦄ public

