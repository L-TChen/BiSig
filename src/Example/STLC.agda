open import Prelude
  hiding (_↣_)

module Example.STLC where

import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 -- base type
  ∷ 2   -- function type
  ∷ []

open import Syntax.Simple.Term ΛₜD       as Type
  using (`_; op)
  renaming (Tm₀ to Λₜ)
open import Syntax.Context Λₜ

infixr 8 _↣_
pattern _↣_ A B = op (inr (inl (A , B ,  _)))

open import Syntax.Typed.Description ΛₜD as T

ΛₒD : Desc
ΛₒD =
  σ[ A ] σ[ B ] ▷ ρ[ ⊢ ` (A , suc zero) ↣ ` (B , zero) ] ρ[ ⊢ ` (A , suc zero) ] ι ⦂ ` (B , zero) ∷
  σ[ A ] σ[ B ] ▷ ρ[ ` (A , suc zero) ∙ ⊢ ` (B , zero) ] ι ⦂ (` (A , suc zero) ↣ ` (B , zero)) ∷
  []
{-
    σ[ A ] σ[ B ] ▷ ρ[ ⊢ A ↣ B ] ρ[ ⊢ A ] ι ⦂ B      -- application
  ∷ σ[ A ] σ[ B ] ▷ ρ[ A ∷ ⊢ B ] ι          ⦂ A ↣ B  -- abstraction
  ∷ []

-}

open import Syntax.Typed.Term    ΛₒD
private variable
  A B : Λₜ
  Γ Δ : Ctx

pattern ƛ_  t   = op (inr (inl (_ , _ , refl , t , _)))
pattern _·_ t u = op (inl (_ , _ , refl , t , u , _)) 

𝐼 : ∀ {A} → Tm (A ↣ A) Γ
𝐼 {A = A} = ƛ ` zero

𝐾₁ : Tm (A ↣ B ↣ A) Γ
𝐾₁ = ƛ ƛ ` suc zero

_ : Tm A (A ∙ Γ)
_ = 𝐼 · ` zero

height : Tm A Γ → ℕ
height (` x)   = 0
height (t · u) = suc (height t ⊔ height u)
height (ƛ t)   = suc (height t)
