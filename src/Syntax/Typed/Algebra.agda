open import Prelude

import Syntax.Simple.Description as S
import Syntax.Typed.Description  as Typed

module Syntax.Typed.Algebra {SD : S.Desc} (D : Typed.Desc SD) where
open Typed SD
open import Syntax.Simple.Term SD
  using ()
  renaming (Tm₀ to T)
open import Syntax.Typed.Context T

-- relative continuation monad
record Cont (Val : Set) {A : Set} (Γ : A → Set) : Set where
  constructor cont
  field runCont : (∀ {x : A} → Γ x → Val) → Val
open Cont public

-- var height n        .runCont ρ = ρ n
-- alg height (o , ts) .runCont   = suc ∘ algᶜ (arity s o) ts .runCont
--   where
--     algᶜ : ∀ as → ? -- (as -Algᶜ) (Cont ℕ)
--     algᵇ : ∀ a  → (a  -Algᵇ) (Cont ℕ)
--     algᵇ zero    t = t
--     algᵇ (suc a) t .runCont ρ = algᵇ a t .runCont λ where zero → 0; (suc x) → ρ x
--     algᶜ []       t       .runCont _ = 0
--     algᶜ (x ∷ as) (t , u) .runCont ρ = algᵇ x t .runCont ρ ⊔ algᶜ as u .runCont ρ
-- 
-- -- remove zeros and strengthen (suc n) to n
-- strengthen : ∀ {n} → List (Fin (suc n)) → List (Fin n)
-- strengthen []           = []
-- strengthen (zero  ∷ xs) = strengthen xs
-- strengthen (suc x ∷ xs) = x ∷ strengthen xs
-- 
-- fv : (s -Alg) (List ∘ Fin)
-- var fv n        = n ∷ []
-- alg fv (o , ts) = algᶜ (arity s o) ts
--   where
--     algᵇ : ∀ a → (a -Algᵇ) (List ∘ Fin)
--     algᵇ zero    t = t
--     algᵇ (suc a) t = strengthen (algᵇ a t)
-- 
--     algᶜ : ∀ as → (as -Algᶜ) (List ∘ Fin)
--     algᶜ []       _       = []
--     algᶜ (a ∷ as) (t , u) = algᵇ a t ++ algᶜ as u