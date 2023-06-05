{-# OPTIONS --safe #-}

module Example.STLC where

open import Prelude
  hiding (_↣_)

open import Example.Implicational

open import Syntax.Typed.Description ΛₜD
  renaming (_⊢_ to infix 4 _⊢_)

data ΛOp : Set where
  `app `abs : ΛOp

decΛOp : DecEq ΛOp
decΛOp = record { _≟_ = dec }
  where
    dec : ∀ x y → Dec (x ≡ y)
    dec `app `app = yes refl
    dec `app `abs = no λ ()
    dec `abs `app = no λ ()
    dec `abs `abs = yes refl

ΛₒD : Desc
ΛₒD = record
  { Op    = ΛOp
  ; decOp = decΛOp
  ; rules = λ { `app → 2 ▷ ρ[ [] ⊢ ` # 1 ↣ ` # 0 ]  ρ[ [] ⊢ ` # 1 ] [] ⦂ ` # 0
              ; `abs → 2 ▷ ρ[ ` # 1 ∷ [] ⊢ ` # 0 ]                  [] ⦂ ` # 1 ↣ ` # 0 } }

open import Syntax.Typed.Intrinsic.Term ΛₒD

private variable
  m n : ℕ
  A B : Λₜ  m
  Γ Δ : Cxt m

pattern _·_ t u  = op (`app , _ ∷ _ ∷ [] , refl , t , u , _)
pattern ƛ_ t     = op (`abs , _ ∷ _ ∷ [] , refl , t , _)

infixl 8 _·_
infixr 7 ƛ_

𝑰 : Tm _ (A ↣ A) Γ
𝑰 = ƛ ` here refl

𝐾₁ : Tm _ (A ↣ B ↣ A) Γ
𝐾₁  = ƛ ƛ ` there (here refl)

_ : Tm _ A (A ∷ Γ)
_ = 𝑰 · ` here refl

{-
height : Tm _ A Γ → ℕ
height (` x)   = 0
height (t · u) = suc (height t ⊔ height u)
height (ƛ t)   = suc (height t)
-}
