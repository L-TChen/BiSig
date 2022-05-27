open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Term {O : Set} (s : Signature O) where

infix 40 `_

data Tm : ℕ → Set where
  `_ : Fin      ⇒ Tm
  op : ⟦ s ⟧ Tm ⇒ Tm

module _ {T : ℕ → Set ℓ} (α : s -Alg T) where
  fold : Tm ⇒ T
  foldMap  : (s : Signature O) → ⟦ s ⟧   Tm ⇒ ⟦ s ⟧   T
  foldMapᶜ : (as : List ℕ)     → ⟦ as ⟧ᶜ Tm ⇒ ⟦ as ⟧ᶜ T
  foldMapᵇ : (a : ℕ)           → ⟦ a ⟧ᵇ  Tm ⇒ ⟦ a ⟧ᵇ  T

  fold (` x)  = α .var x
  fold (op x) = α .alg (foldMap s x)

  foldMap (sig ar) (o , as) = o , foldMapᶜ (ar o) as

  foldMapᶜ []       _       = _
  foldMapᶜ (a ∷ as) (t , u) = foldMapᵇ a t , foldMapᶜ as u

  foldMapᵇ zero    t = fold t
  foldMapᵇ (suc a) t = foldMapᵇ a t

heightAlg : s -Alg (Cont ℕ)
var heightAlg n        .runCont ρ = ρ n
alg heightAlg (o , ts) .runCont   = suc ∘ algᶜ (arity s o) ts .runCont
  where
    algᶜ : ∀ as → ⟦ as ⟧ᶜ Cont ℕ ⇒ Cont ℕ
    algᵇ : ∀ a  → ⟦ a  ⟧ᵇ Cont ℕ ⇒ Cont ℕ
    algᵇ zero    t = t
    algᵇ (suc a) t .runCont ρ = algᵇ a t .runCont λ where
      zero → 0; (suc x) → ρ x
    algᶜ []       t       .runCont _ = 0
    algᶜ (x ∷ as) (t , u) .runCont ρ = algᵇ x t .runCont ρ ⊔ algᶜ as u .runCont ρ
 
height : ∀ {n} → Tm n → ℕ
height t = fold heightAlg t .runCont (λ _ → 0)
