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

open import Syntax.Typed.Raw.Term ΛₒD

private variable
  m n   : ℕ
  A B C : Λₜ  0
  Γ Δ   : Cxt 0

infixl 8 _·_
infixr 7 ƛ_

pattern _·_ r s = op (`app , r , s , _)
pattern ƛ_  r   = op (`abs , r , _)

S : Raw n
S = ƛ ƛ ƛ ` suc (suc zero) · ` zero · (` suc zero · ` zero)

height : Raw n → ℕ
height (` i)   = 0
height (_ ∋ r) = height r
height (r · s) = suc (height r ⊔ height s)
height (ƛ r)   = suc (height r)

open import Syntax.Typed.Term ΛₒD

infixl 8 _·ᵀ_
infixr 7 ƛᵀ_

pattern _·ᵀ_ t u = op (_ ∷ _ ∷ [] , refl , t , u , _)
pattern ƛᵀ_  t   = op (_ ∷ _ ∷ [] , refl , t , _)

⊢S : Γ ⊢ S ⦂ (A ↣ B ↣ C) ↣ (A ↣ B) ↣ A ↣ C
⊢S = ƛᵀ ƛᵀ ƛᵀ ` there (there (here refl)) ·ᵀ ` here refl ·ᵀ
                    (` there (here refl)  ·ᵀ ` here refl)
