{-# OPTIONS --with-K #-}
open import Prelude
import Syntax.Typed.Signature as S

module Syntax.Typed.DecOp {T O : Set} (_≟o_ : Decidable {A = O} _≡_) (s : S.Sig T O) where

open import Syntax.Typed.Context T
open import Syntax.Typed.Term s
open S T

private variable
  A B : T
  Γ Δ : Ctx

_≟ᵢ_ : (x y : A ∈ Γ) → Dec (x ≡ y)
zero  ≟ᵢ zero  = yes refl
suc x ≟ᵢ suc y with x ≟ᵢ y
... | yes refl = yes refl
... | no ¬p = no λ where refl → ¬p refl
zero  ≟ᵢ suc _ = no λ ()
suc _ ≟ᵢ zero  = no λ ()

mutual
  _≟_ : (t u : Tm A Γ) → Dec (t ≡ u)
  (` x) ≟ (` y) with x ≟ᵢ y
  ... | yes refl = yes refl
  ... | no ¬p = no λ where refl → ¬p refl
  op (o₁ , eq₁ , ts) ≟ op (o₂ , eq₂ , us) with o₁ ≟o o₂
  ... | no ¬p = no λ where refl → ¬p refl
  (op (o₁ , refl , ts) ≟ op (o₁ , refl , us)) | yes refl with compareMap (arity s o₁) ts us
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl = yes refl
  ` _ ≟ op _ = no λ ()
  op _ ≟ ` _ = no λ ()

  compareMap : ∀ as {Γ} → (t u : (⟦ as ⟧ᵃ Tm) Γ) → Dec (t ≡ u)
  compareMap ∅        _ _ = yes refl
  compareMap (a ∙ as) (t , ts) (u , us) with compareMapᵇ a t u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMap as ts us
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl

  compareMapᵇ : ∀ a {Γ} → (t u : (⟦ a ⟧ᵇ Tm) Γ) → Dec (t ≡ u)
  compareMapᵇ (∅       , A) t u = t ≟ u
  compareMapᵇ ((B ∙ Δ) , A) t u = compareMapᵇ (Δ , A) t u