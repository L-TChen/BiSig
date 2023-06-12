{-# OPTIONS --safe #-}

module Example.STLC where

open import Prelude
  hiding (_↣_)

variable
  n : ℕ
  d : Mode

import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 -- base type
    ∷ 2 -- function type
    ∷ []

{-
data Λₜ : Set where
  ι   :              Λₜ
  _↣_ : (A B : Λₜ) → Λₜ
-}

open import Syntax.Simple.Term ΛₜD
  using (`_; op)
  renaming (Tm to Λₜ)

open import Syntax.Context ΛₜD

variable
  A B C : Λₜ  0
  Γ Δ   : Cxt 0

infixr 8 _↣_

pattern _↣_ A B = op (2 , there (here refl) , A ∷ B ∷ [])

open import Syntax.BiTyped.Description ΛₜD

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

Λ⇔D : Desc
Λ⇔D = record
  { Op    = ΛOp
  ; decOp = decΛOp
  ; rules = λ { `app → 2 ▷ ρ[ [] ⊢[ Syn ] ` # 1 ↣ ` # 0 ]
                           ρ[ [] ⊢[ Chk ] ` # 1 ] [] ⇒ ` # 0
                    -- Γ ⊢ t ⇒ (A → B)    Γ ⊢ u ⇐ A
                    -- ----------------------------
                    --   Γ ⊢ t u ⇒ B
              ; `abs → 2 ▷ ρ[ (` # 1 ∷ []) ⊢[ Chk ] ` # 0 ] [] ⇐ (` # 1) ↣ (` # 0) } }
                    -- Γ , x : A ⊢ t ⇐ B
                    -----------------------
                    -- Γ ⊢ λ x . t ⇐ A → B

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase Λ⇔D)

infixl 8 _·_
infixr 7 ƛ_

pattern _·_ r s = op (`app , r , s , _)
pattern ƛ_  r   = op (`abs , r , _)

S : Raw n
S = ƛ ƛ ƛ ` suc (suc zero) · ` zero · (` suc zero · ` zero)

open import Syntax.BiTyped.Term Λ⇔D

infixl 8 _·ᴮ_
infixr 7 ƛᴮ_

pattern _·ᴮ_ t u = op (refl , _ ∷ _ ∷ [] , refl , t , u , _)
pattern ƛᴮ_  t   = op (refl , _ ∷ _ ∷ [] , refl , t , _)

⊢S : Γ ⊢ S ⇐ (A ↣ B ↣ C) ↣ (A ↣ B) ↣ A ↣ C
⊢S = ƛᴮ ƛᴮ ƛᴮ ((` there (there (here refl)) ·ᴮ ((` here refl) ↑ refl) ·ᴮ
                     ((` there (here refl)  ·ᴮ ((` here refl) ↑ refl)) ↑ refl)) ↑ refl)
