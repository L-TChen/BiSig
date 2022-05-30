open import Prelude
  hiding (_↣_)

module Example.STLC where

infixr 5 _↣_
data Λₜ : Set where
  ι   : Λₜ
  _↣_ : (A B : Λₜ) → Λₜ

open import Syntax.Context         Λₜ
open import Syntax.Typed.Signature Λₜ

private variable
  A B : Λₜ
  Γ   : Ctx

data Λₒ : Set where
  app : {A B : Λₜ} → Λₒ
  abs : {A B : Λₜ} → Λₒ

Λ∶Sig : Sig Λₒ
∣ Λ∶Sig ∣ = λ where
  (app {A} {B}) → ([] , A ↣ B) ∷ ([] , A) ∷ [] , B
  (abs {A} {B}) → (A ∷ [] , B) ∷ [] , A ↣ B

open import Syntax.Typed.Term Λ∶Sig
 
infixl 6 _·_
infixr 5 ƛ_
pattern ƛ_  t   = op (abs , refl , t , _)
pattern _·_ t u = op (app , refl , t , u , _)

𝐼 : Tm (A ↣ A) Γ
𝐼 = ƛ ` zero

K₁ : Tm (A ↣ B ↣ A) ∅
K₁ = ƛ ƛ ` suc zero

K₂ : Tm (A ↣ B ↣ B) ∅
K₂ = ƛ ƛ ` zero

_ : Tm A (A ∙ ∅)
_ = 𝐼 · ` zero

h : Tm A Γ → ℕ
h (` x)   = 0
h (ƛ t)   = suc (h t)
h (t · u) = suc (h t ⊔ h u)