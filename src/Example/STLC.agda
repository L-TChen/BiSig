{-# OPTIONS --safe #-}

module Example.STLC where

open import Prelude
  hiding (_↣_)

open import Example.Implicational

open import Syntax.Typed.Description {ΛₜD}
  renaming (_⊢_ to infix 4 _⊢_)

ΛₒD : Desc
ΛₒD =
  2 ▷ ρ[ [] ⊢ ` # 1 ↣ ` # 0 ]  ρ[ [] ⊢ ` # 1 ] [] ⦂ ` # 0         ∷
  2 ▷ ρ[ ` # 1 ∷ [] ⊢ ` # 0 ]                 [] ⦂ ` # 1 ↣ ` # 0 ∷
  []
{-
    σ[ A ] σ[ B ] ▷ ρ[ ⊢ A ↣ B ] ρ[ ⊢ A ] ι ⦂ B      -- application
  ∷ σ[ A ] σ[ B ] ▷ ρ[ A ∷ ⊢ B ] ι          ⦂ A ↣ B  -- abstraction
  ∷ []
-}

open import Syntax.Typed.Intrinsic.Term ΛₒD

private variable
  m n : ℕ
  A B : Λₜ  m
  Γ Δ : Cxt m

pattern ƛ_ t     = op (_ , there (here refl) , _ ∷ _ ∷ [] , refl , t , _)
pattern _·_ t u  = op (_ , here refl , _ ∷ _ ∷ [] , refl , t , u , _)

infixl 8 _·_
infixr 7 ƛ_

𝑰 : Tm _ (A ↣ A) Γ
𝑰 = ƛ ` here refl

𝐾₁ : Tm _ (A ↣ B ↣ A) Γ
𝐾₁  = ƛ ƛ ` there (here refl)

_ : Tm _ A (A ∷ Γ)
_ = 𝑰 · ` here refl

height : Tm _ A Γ → ℕ
height (` x)   = 0
height (t · u) = suc (height t ⊔ height u)
height (ƛ t)   = suc (height t)
