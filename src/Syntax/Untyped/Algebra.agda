open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Algebra {O : Set} (s : Sig O) where

padding : ∀ {n} → (Fin n → ℕ) → (Fin (suc n) → ℕ)
padding ρ zero    = zero
padding ρ (suc x) = ρ x

height : (s -Alg) (Cont ℕ)
var height n        .runCont ρ = ρ n
alg height (o , ts) .runCont   = suc ∘ algᶜ (arity s o) ts .runCont
  where
    algᵇ : ∀ a  → (a -Algᵇ) (Cont ℕ)
    algᵇ zero    t .runCont ρ = t .runCont ρ
    algᵇ (suc a) t .runCont ρ = algᵇ a t .runCont (padding ρ)

    algᶜ : ∀ as → (as -Algᵃ) (Cont ℕ)
    algᶜ []       t       .runCont _ = 0
    algᶜ (a ∷ as) (t , u) .runCont ρ = algᵇ a t .runCont ρ ⊔ algᶜ as u .runCont ρ

-- remove zeros and strengthen (suc n) to n
strengthen : ∀ {n} → List (Fin (suc n)) → List (Fin n)
strengthen []           = []
strengthen (zero  ∷ xs) = strengthen xs
strengthen (suc x ∷ xs) = x ∷ strengthen xs

fv : (s -Alg) (List ∘ Fin)
var fv n        = n ∷ []
alg fv (o , ts) = algᶜ (arity s o) ts
  where
    algᵇ : ∀ a → (a -Algᵇ) (List ∘ Fin)
    algᵇ zero    t = t
    algᵇ (suc a) t = strengthen (algᵇ a t)

    algᶜ : ∀ as → (as -Algᵃ) (List ∘ Fin)
    algᶜ []       _       = []
    algᶜ (a ∷ as) (t , u) = algᵇ a t ++ algᶜ as u