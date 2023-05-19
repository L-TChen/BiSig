{-# OPTIONS --safe #-}

module Example.BiSTLC where

open import Prelude
  hiding (_↣_)

open import Example.Implicational
open import Example.STLC using (ΛOp; `app; `abs; decΛOp)

private variable
  T     : Set
  mod   : Mode
  m n   : ℕ
  A B C : Λₜ  n
  Γ Δ   : Cxt n

open import Syntax.BiTyped.Description ΛₜD

Λ⇆D : Desc
Λ⇆D = record
  { Op    = ΛOp
  ; decOp = decΛOp
  ; rules = λ { `app → 2 ▷ ρ[ [] ⇉ (` # 1) ↣ (` # 0) ] ρ[ [] ⇇ ` # 1 ] [] ⇉ ` # 0
                    -- Γ ⊢ t ⇉ (A → B)    Γ ⊢ u ⇇ A
                    -- ----------------------------
                    --   Γ ⊢ t u ⇉ B
              ; `abs → 2 ▷ ρ[ ` # 1 ∷ [] ⇇ ` # 0 ] [] ⇇ (` # 1) ↣ (` # 0) } }
                    -- Γ , x : A ⊢ t ⇇ B
                    -----------------------
                    -- Γ ⊢ λ x . t ⇇ A → B

open import Syntax.BiTyped.Intrinsic.Term Λ⇆D

pattern ƛ′_  t   = op (`abs , refl , _ ∷ _ ∷ [] , refl , t , _)
pattern _·′_ t u = op (`app , refl , _ ∷ _ ∷ [] , refl , t , u , _)

mutual
  data Λ⇉ {m : ℕ} : Λₜ m → Cxt m → Set where
    `_ : _∈_ ⇒ Λ⇉
    _·_
      : (t : Λ⇉ (A ↣ B) Γ) (u : Λ⇇ A Γ)
      → Λ⇉ B Γ
    _∋_
      : (A : Λₜ m) (t : Λ⇇ A Γ)
      → Λ⇉ A Γ

  data Λ⇇ {m : ℕ} : Λₜ m → Cxt m → Set where
    ƛ_
      : (t : Λ⇇ B (A ∷ Γ))
      → Λ⇇ (A ↣ B) Γ
    ⇉_by_
      : (t : Λ⇉ A Γ) (eq : B ≡ A)
      → Λ⇇ B Γ

Λ : Mode → Λₜ m → Cxt m → Set
Λ Check = Λ⇇
Λ Infer = Λ⇉

toΛ : Tm _ mod A Γ → Λ mod A Γ
toΛ (` x)       = ` x
toΛ (_ ∋ t)     = _ ∋ toΛ t
toΛ (⇉ t by eq) = ⇉ (toΛ t) by eq
toΛ (t ·′ u)    = toΛ t · toΛ u
toΛ (ƛ′ t)      = ƛ toΛ t

fromΛ : ∀ mod → Λ mod A Γ → Tm _ mod A Γ
fromΛ Infer (` x)       = ` x
fromΛ Infer (_ ∋ t)     = _ ∋ fromΛ Check t
fromΛ Check (⇉ t by eq) = ⇉ fromΛ Infer t by eq
fromΛ Infer (t · u)     = fromΛ Infer t ·′ fromΛ Check u
fromΛ Check (ƛ t)       = ƛ′ (fromΛ Check t)

from-toΛ : (t : Tm _ mod A Γ) → fromΛ mod (toΛ t) ≡ t
from-toΛ (` x)       = refl
from-toΛ (_ ∋ t)     = cong (_ ∋_) (from-toΛ t)
from-toΛ (⇉ t by eq) = cong (⇉_by eq)  (from-toΛ t)
from-toΛ (t ·′ u)    = cong₂ _·′_ (from-toΛ t) (from-toΛ u)
from-toΛ (ƛ′ t)      = cong ƛ′_ (from-toΛ t)

to-fromΛ : ∀ mod → (t : Λ mod A Γ) → toΛ (fromΛ mod t) ≡ t
to-fromΛ Infer (` x)       = refl
to-fromΛ Infer (t · u)     = cong₂ _·_ (to-fromΛ _ t) (to-fromΛ _ u)
to-fromΛ Infer (_ ∋ t)     = cong (_ ∋_) (to-fromΛ _ t)
to-fromΛ Check (ƛ t)       = cong ƛ_ (to-fromΛ _ t)
to-fromΛ Check (⇉ t by eq) = cong (⇉_by eq) (to-fromΛ _ t)
