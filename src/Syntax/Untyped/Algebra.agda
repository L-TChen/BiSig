open import Prelude
open import Syntax.Untyped.Signature

module Syntax.Untyped.Algebra {O : Set} (s : Sig O) where

padding : ∀ {l n} → (Fin n → ℕ) → (Fin (l + n) → ℕ)
padding {zero}    ρ = ρ
padding {suc l} ρ zero    = zero
padding {suc l} ρ (suc x) = padding ρ x

height : (s -Alg) (Cont ℕ)
var height n        .runCont ρ = ρ n
alg height (o , ts) .runCont   = suc ∘ algᶜ (arity s o) ts .runCont
  where
    algᶜ : ∀ as → (as -Algᵃ) (Cont ℕ)
    algᶜ []       t       .runCont _ = 0
    algᶜ (a ∷ as) (t , u) .runCont ρ = t .runCont (padding ρ) ⊔ algᶜ as u .runCont ρ

-- remove zeros and strengthen (suc n) to n
strengthen : ∀ {n} → List (Fin (suc n)) → List (Fin n)
strengthen []           = []
strengthen (zero  ∷ xs) = strengthen xs
strengthen (suc x ∷ xs) = x ∷ strengthen xs

strengthenⁿ : ∀ l {n} → List (Fin (l + n)) → List (Fin n)
strengthenⁿ zero    xs = xs
strengthenⁿ (suc l) xs = strengthenⁿ l (strengthen xs)

fv : (s -Alg) (List ∘ Fin)
var fv n        = n ∷ []
alg fv (o , ts) = algᶜ (arity s o) ts
  where
    algᶜ : ∀ as → (as -Algᵃ) (List ∘ Fin)
    algᶜ []       _       = []
    algᶜ (a ∷ as) (t , u) = strengthenⁿ a t ++ algᶜ as u