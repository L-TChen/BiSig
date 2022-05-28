open import Prelude

-- Untyped Lambda Calculus
module Example.ULC where

open import Syntax.Untyped.Signature

data Λₒ : Set where
  app abs : Λₒ

Λ∶Sig : Sig Λₒ
∣ Λ∶Sig ∣ = λ where
  app → 0 ∷ 0 ∷ []
  abs → 1 ∷ []

open import Syntax.Untyped.Term Λ∶Sig renaming (Tm to Λ)
open import Syntax.Untyped.Raw  String _≟s_ Λ∶Sig

pattern ƛ_  t   = op (abs , t , _)
pattern ƛ_↦_ x t = op (abs , (x , t) , _)
pattern _·_ t u = op (app , t , u , _)

identity : Λ 0
identity = ƛ ` (# 0)

t₁ : Λ 0
t₁ = ƛ ƛ (` (# 0) · ` (# 1))

rt : Raw
rt = ƛ "x" ↦ ƛ "y" ↦ ` "x"

ρ : String → Fin 1
ρ _ = zero

_ : fromRaw ρ rt ≡ (ƛ ƛ (` (# 1)))
_ = refl