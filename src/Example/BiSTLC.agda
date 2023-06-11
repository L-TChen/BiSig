{-# OPTIONS --safe #-}

module Example.BiSTLC where

open import Prelude
  hiding (_↣_)

open import Example.Implicational
open import Example.STLC using (ΛOp; `app; `abs; decΛOp)

variable
  n     : ℕ
  d     : Mode
  A B C : Λₜ  0
  Γ Δ   : Cxt 0

open import Syntax.BiTyped.Description ΛₜD

Λ⇔D : Desc
Λ⇔D = record
  { Op    = ΛOp
  ; decOp = decΛOp
  ; rules = λ { `app → 2 ▷ ρ[ [] ⊢[ Inf ] ` # 1 ↣ ` # 0 ]
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
