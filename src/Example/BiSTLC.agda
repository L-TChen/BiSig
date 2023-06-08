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
  ; rules = λ { `app → 2 ▷ ρ[ [] ⊢[ Syn ] ` # 1 ↣ ` # 0 ]
                           ρ[ [] ⊢[ Chk ] ` # 1 ] [] ⇒ ` # 0
                    -- Γ ⊢ t ⇉ (A → B)    Γ ⊢ u ⇇ A
                    -- ----------------------------
                    --   Γ ⊢ t u ⇉ B
              ; `abs → 2 ▷ ρ[ (` # 1 ∷ []) ⊢[ Chk ] ` # 0 ] [] ⇐ (` # 1) ↣ (` # 0) } }
                    -- Γ , x : A ⊢ t ⇇ B
                    -----------------------
                    -- Γ ⊢ λ x . t ⇇ A → B

open import Syntax.BiTyped.Intrinsic.Term Λ⇆D

pattern lam ρ t   = op (`abs , refl , ρ , refl , t , _)
pattern app ρ t u = op (`app , refl , ρ , refl , t , u , _)

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
    _↑by_
      : (t : Λ⇉ A Γ) (eq : B ≡ A)
      → Λ⇇ B Γ

Λ : Mode → Λₜ m → Cxt m → Set
Λ Chk = Λ⇇
Λ Syn = Λ⇉

toΛ : Tm _ mod A Γ → Λ mod A Γ
toΛ (` x)      = ` x
toΛ (_ ∋ t)    = _ ∋ toΛ t
toΛ (t ↑by eq) = (toΛ t) ↑by eq
toΛ (app ρ t u)   = toΛ t · toΛ u
toΛ (lam ρ t)     = ƛ toΛ t

fromΛ : ∀ mod → Λ mod A Γ → Tm _ mod A Γ
fromΛ Syn (` x)       = ` x
fromΛ Syn (_ ∋ t)     = _ ∋ fromΛ Chk t
fromΛ Chk (t ↑by eq) = fromΛ Syn t ↑by eq
fromΛ Syn (t · u)     = app (λ { zero → _ ; (suc zero) → _}) (fromΛ Syn t) (fromΛ Chk u)
fromΛ Chk (ƛ t)       = lam (λ { zero → _ ; (suc zero) → _}) (fromΛ Chk t)

-- to-fromΛ : ∀ mod → (t : Λ mod A Γ) → toΛ (fromΛ mod t) ≡ t
-- to-fromΛ Syn (` x)      = refl
-- to-fromΛ Syn (t · u)    = cong₂ _·_ (to-fromΛ _ t) (to-fromΛ _ u)
-- to-fromΛ Syn (_ ∋ t)    = cong (_ ∋_) (to-fromΛ _ t)
-- to-fromΛ Chk (ƛ t)      = cong ƛ_ (to-fromΛ _ t)
-- to-fromΛ Chk (t ↑by eq) = cong (_↑by eq) (to-fromΛ _ t)
