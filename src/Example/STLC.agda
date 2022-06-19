open import Prelude
  hiding (_↣_)

module Example.STLC where

import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 -- base type
  ∙ 2   -- function type
  ∙ ∅

open import Syntax.Simple.Term ΛₜD   as Type
  using (`_; op)
  renaming (Tm₀ to Λₜ)
open import Syntax.Context

infixr 8 _↣_
pattern _↣_ A B = op (_ , there (here refl) , A , B , _)

open import Syntax.Typed.Description {ΛₜD} as T
  renaming (_⊢_ to infix 4 _⊢_)

ΛₒD : Desc 
ΛₒD =
  2 ▷ ρ[ ∅ ⊢ ` # 1 ↣ ` # 0 ]  ρ[ ∅ ⊢ ` # 1 ] ∅ ⦂ ` # 0 ∙
  2 ▷ ρ[ ` # 1 ∙ ∅ ⊢ ` # 0 ]                 ∅ ⦂ ` # 1 ↣ ` # 0 ∙
  ∅
{-
    σ[ A ] σ[ B ] ▷ ρ[ ⊢ A ↣ B ] ρ[ ⊢ A ] ι ⦂ B      -- application
  ∷ σ[ A ] σ[ B ] ▷ ρ[ A ∷ ⊢ B ] ι          ⦂ A ↣ B  -- abstraction
  ∷ []
-}

open import Syntax.Typed.Intrinsic.Term  ΛₒD
private variable
  A B : Λₜ
  Γ Δ : Ctx Λₜ

pattern ƛ_ t     = op (_ , there (here refl) , _ ∷ _ ∷ [] , refl , t , _)
pattern _·_ t u  = op (_ , here refl , _ ∷ _ ∷ [] , refl , t , u , _)

infixl 8 _·_
infixr 7 ƛ_ 

𝑰 : ∀  {A} → Tm (A ↣ A) Γ
𝑰 = ƛ ` here refl

𝐾₁ : Tm (A ↣ B ↣ A) Γ
𝐾₁  = ƛ ƛ ` there (here refl)

_ : Tm A (A ∙ Γ)
_ = 𝑰 · ` here refl

height : Tm A Γ → ℕ
height (` x)   = 0
height (t · u) = suc (height t ⊔ height u)
height (ƛ t)   = suc (height t)