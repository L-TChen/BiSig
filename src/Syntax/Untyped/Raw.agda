open import Prelude
import Syntax.Untyped.Signature as S

module Syntax.Untyped.Raw (Id : Set) (_≟_ : Decidable {A = Id} _≡_) {O : Set} (s : S.Sig O) where

open import Syntax.Untyped.Term             s
open import Syntax.Untyped.Raw.Term      Id s public
open import Syntax.Untyped.Raw.Signature Id

private
  variable
    n m : ℕ

_∙_ : Id → (Id → Fin n) → Id → Fin (suc n)
(x ∙ ρ) y with x ≟ y
... | yes p = zero
... | no ¬p = suc (ρ y)

_∙∙_ : ∀ {a} → Id ^ a → (Id → Fin n) → Id → Fin (a + n)
_∙∙_ {a = zero}  _        ρ = ρ
_∙∙_ {a = suc a} (xs , x) ρ = x ∙ (xs ∙∙ ρ)

mutual
  fromRaw : (Id → Fin n)
    → Raw → Tm n 
  fromRaw ρ (` x)         = ` ρ x
  fromRaw ρ (op (f , ts)) = op (f , (fromRawMapᶜ (S.arity s f) ρ ts))

  fromRawMapᶜ : ∀ as → (Id → Fin n) → ⟦ as ⟧ᶜ Raw → (S.⟦ as ⟧ᵃ Tm) n
  fromRawMapᶜ []       ρ _               = _
  fromRawMapᶜ (a ∷ as) ρ ((ids , t) , u) = fromRaw (ids ∙∙ ρ) t , (fromRawMapᶜ as ρ u)