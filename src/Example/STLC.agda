open import Prelude
  hiding (_↣_)

module Example.STLC where

import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 -- base type
  ∷ 2   -- function type
  ∷ []

open import Syntax.Simple.Term ΛₜD   as Type
  using (`_; op)
  renaming (Tm₀ to Λₜ)
open import Syntax.Context

infixr 8 _↣_
pattern _↣_ A B = op (inr (inl (A , B ,  _)))

open import Syntax.Typed.Description {ΛₜD} as T

ΛₒD : Desc 
ΛₒD =
  2 ▷ ρ[ ⊢ ` # 0 ↣ ` # 1 ] ρ[ ⊢ ` # 0 ] ι ⦂ (` # 1) ∷
  2 ▷ ρ[ ` # 0 ∙ ⊢ ` # 1 ] ι ⦂ (` # 0 ↣ ` # 1)      ∷
  []
{-
    σ[ A ] σ[ B ] ▷ ρ[ ⊢ A ↣ B ] ρ[ ⊢ A ] ι ⦂ B      -- application
  ∷ σ[ A ] σ[ B ] ▷ ρ[ A ∷ ⊢ B ] ι          ⦂ A ↣ B  -- abstraction
  ∷ []
-}

open import Syntax.Typed.Term  ΛₒD
private variable
  A B : Λₜ
  Γ Δ : Ctx Λₜ

pattern ƛ_ t = op (inr (inl ((_ ∷ _ ∷ []) , refl , t , _)))
pattern _·_ t u = op (inl ((_ ∷ _ ∷ []) , refl , t , u , _)) 
infixl 8 _·_
infixr 7 ƛ_ 

𝑰 : ∀ {A} → Tm (A ↣ A) Γ
𝑰 = ƛ ` zero

𝐾₁ : Tm (A ↣ B ↣ A) Γ
𝐾₁  = ƛ ƛ ` suc zero

_ : Tm A (A ∙ Γ)
_ = 𝑰 · ` zero

height : Tm A Γ → ℕ
height (` x)   = 0
height (t · u) = suc (height t ⊔ height u)
height (ƛ t)   = suc (height t)