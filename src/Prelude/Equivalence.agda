module Prelude.Equivalence where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Level

private variable
  a b c : Level
  A B : Set a

------------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------------

record Equivalence (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    to   : A → B
    from : B → A
open Equivalence

infix 3 _⇔_
_⇔_ : Set a → Set b → Set _
A ⇔ B = Equivalence A B

≡to⟺ : A ≡ B → A ⇔ B
≡to⟺ eq .to   = subst (λ A → A) eq
≡to⟺ eq .from = subst (λ A → A) (sym eq)

⇔-sym : A ⇔ B → B ⇔ A
⇔-sym equiv .to   = from equiv
⇔-sym equiv .from = to equiv

Dec⇔ : A ⇔ B → Dec A → Dec B
Dec⇔ equiv = map′ (to equiv) (from equiv)
