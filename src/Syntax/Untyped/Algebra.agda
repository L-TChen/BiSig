open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Algebra {O : Set} (s : Sig O) where

height : (s -Alg) (Cont ℕ)
var height n        .runCont ρ = ρ n
alg height (o , ts) .runCont   = suc ∘ algᶜ (arity s o) ts .runCont
  where
    algᶜ : ∀ as → (as -Algᶜ) (Cont ℕ)
    algᵇ : ∀ a  → (a  -Algᵇ) (Cont ℕ)
    algᵇ zero    t = t
    algᵇ (suc a) t .runCont ρ = algᵇ a t .runCont λ where zero → 0; (suc x) → ρ x
    algᶜ []       t       .runCont _ = 0
    algᶜ (x ∷ as) (t , u) .runCont ρ = algᵇ x t .runCont ρ ⊔ algᶜ as u .runCont ρ

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

    algᶜ : ∀ as → (as -Algᶜ) (List ∘ Fin)
    algᶜ []       _       = []
    algᶜ (a ∷ as) (t , u) = algᵇ a t ++ algᶜ as u