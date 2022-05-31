open import Prelude

module Generic.Erasure.Type {T O : Set} where

open import Syntax.Typed.Signature   T as Typed
open import Syntax.Untyped.Signature   as Untyped
  hiding (Ctx)
open import Syntax.Typed.Context T

import Data.List as L

private
  variable
    Γ Δ : Ctx
    A   : T

eraseArg : Typed.Arg → Untyped.Arg
eraseArg (Δ , A) = length Δ

eraseₛ : Typed.Sig O → Untyped.Sig O
∣ eraseₛ s ∣ o = L.map eraseArg (Typed.arity s o)

eraseArgs : Typed.Args → Untyped.Args
eraseArgs ∅         = ∅
eraseArgs  (a ∙ as) = eraseArg a ∙ eraseArgs as

eraseᵢ : (A ∈ Γ) → Fin (length Γ)
eraseᵢ zero    = zero
eraseᵢ (suc x) = suc (eraseᵢ x)

open import Syntax.Typed.Term   as Typed
open import Syntax.Untyped.Term as Untyped

module _ {s : Typed.Sig O} where mutual
  erase : Typed.Tm s A Γ → Untyped.Tm (eraseₛ s) (length Γ)
  erase (`  x)               = ` eraseᵢ x
  erase (op (o , refl , ts)) = op (o , {!   !} ) --op (o , {!  eraseMap ? ts !})

  eraseMap : ∀ as
    → (Typed.⟦ as ⟧ᵃ Typed.Tm s) Γ
    → (Untyped.⟦ eraseArgs as ⟧ᵃ Untyped.Tm (eraseₛ s)) (length Γ)
  eraseMap ∅        _        = _
  eraseMap (a ∙ as) (t , ts) = eraseMapᵇ a t , eraseMap as ts

  eraseMapᵇ : ∀ a
    → (Typed.⟦ a ⟧ᵇ Typed.Tm s) Γ
    → (Untyped.⟦ eraseArg a ⟧ᵇ Untyped.Tm (eraseₛ s)) (length Γ)
  eraseMapᵇ (∅       , A) t = erase t
  eraseMapᵇ ((_ ∙ Δ) , A) t = eraseMapᵇ (Δ , A) t