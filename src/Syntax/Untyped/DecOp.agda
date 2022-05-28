open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.DecOp {O : Set} (_≟o_ : Decidable {A = O} _≡_) (s : Sig O) where

import      Data.Fin as F
open import Syntax.Untyped.Term s

private variable
  n m : ℕ

mutual
  _≟_ : Decidable {A = Tm n} _≡_
  (` x) ≟ (` y) with x F.≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl
  op (o₁ , ts)  ≟ op (o₂ , us)  with o₁ ≟o o₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMapᶜ (arity s o₁) ts us
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl = yes refl
  (` x) ≟ op t  = no λ ()
  op x  ≟ (` y) = no λ ()

  compareMapᶜ : ∀ as {n} → Decidable {A = (⟦ as ⟧ᶜ Tm) n } _≡_
  compareMapᶜ []       _        _        = yes refl
  compareMapᶜ (a ∷ as) (t , ts) (u , us) with compareMapᵇ a t u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMapᶜ as ts us
  ... | yes refl = yes refl
  ... | no ¬p = no λ where refl → ¬p refl

  compareMapᵇ : ∀ a {n} → Decidable {A = (⟦ a ⟧ᵇ Tm) n } _≡_
  compareMapᵇ zero    t u = t ≟ u
  compareMapᵇ (suc a) t u = compareMapᵇ a t u