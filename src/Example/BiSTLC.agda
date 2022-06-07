open import Prelude
  hiding (_↣_)

module Example.BiSTLC where

open import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 ∷ 2 ∷ []

open import Syntax.Simple.Term ΛₜD
  using (`_)
  renaming (Tm₀ to Λₜ ; op to top)
open import Syntax.Context Λₜ

infixr 10 _↣_
pattern _↣_ A B = top (inr (inl (A , B , _)))
{-
data Λₜ : Set where
  ι   :              Λₜ
  _↣_ : (A B : Λₜ) → Λₜ
-}

private variable
  A B C : Λₜ
  Γ Δ   : Ctx

open import Syntax.BiTyped.Description ΛₜD as T

ΛₒD : T.Desc
ΛₒD =
  σ[ A ] σ[ B ] ▷
    ρ[ ⇉ ` (A , suc zero) ↣ ` (B , zero) ] ρ[ ⇇ ` (A , suc zero) ] ι
      ⇉ ` (B , zero) ∷
  σ[ A ] σ[ B ] ▷
    ρ[ ` (A , suc zero) ∙ ⇇ ` (B , zero) ] ι
      ⇇ ` (A , suc zero) ↣ ` (B , zero) ∷
  []

open import Syntax.BiTyped.Term ΛₒD

pattern _∙′_ t u = op (inl (_ , _ , refl , refl , t , u , _))
pattern ƛ′_  t   = op (inr (inl (_ , _ , refl , refl , t , _)))
mutual
  data Λ⇉ : Λₜ → Ctx → Set where
    `_ : _∈_ ⇒ Λ⇉
    _∙_
      : (t : Λ⇉ (A ↣ B) Γ) (u : Λ⇇ A Γ)
      → Λ⇉ B Γ
    _∋_
      : (A : Λₜ) (t : Λ⇇ A Γ)
      → Λ⇉ A Γ

  data Λ⇇ : Λₜ → Ctx → Set where
    ƛ_ 
      : (t : Λ⇇ B (A ∙ Γ))
      → Λ⇇ (A ↣ B) Γ
    ⇉_by_
      : (t : Λ⇉ A Γ) (eq : A ≡ B)
      → Λ⇇ B Γ

Λ : Fam₀ -- Mode → Λₜ → Ctx → Set
Λ Check = Λ⇇
Λ Infer = Λ⇉

toΛ : ∀ {m} {A Γ} → Tm m A Γ → Λ m A Γ
toΛ (` x)       = ` x
toΛ (_ ∋ t)     = _ ∋ toΛ t
toΛ (t ∙′ u)    = toΛ t ∙ toΛ u
toΛ (⇉ t by eq) = ⇉ (toΛ t) by eq
toΛ (ƛ′ t)      = ƛ toΛ t
-- toΛ (Tm.op (inr (inr ())))

fromΛ : ∀ m {A Γ} → Λ m A Γ → Tm m A Γ
fromΛ Infer (` x)       = ` x
fromΛ Infer (t ∙ u)     = fromΛ Infer t ∙′ fromΛ Check u
fromΛ Infer (_ ∋ t)     = _ ∋ fromΛ Check t
fromΛ Check (ƛ t)       = ƛ′ fromΛ Check t 
fromΛ Check (⇉ t by eq) = ⇉ fromΛ Infer t by eq

from-toΛ : ∀ {m A Γ}
  → (t : Tm m A Γ)
  → fromΛ m (toΛ t) ≡ t
from-toΛ (` x)       = refl
from-toΛ (_ ∋ t)     = cong (_ ∋_) (from-toΛ t)
from-toΛ (⇉ t by eq) = cong (⇉_by eq)  (from-toΛ t)
from-toΛ (t ∙′ u)    = cong₂ _∙′_ (from-toΛ t) (from-toΛ u)
from-toΛ (ƛ′ t)      = cong ƛ′_ (from-toΛ t)

to-fromΛ : ∀ m {A Γ}
  → (t : Λ m A Γ)
  → toΛ (fromΛ m t) ≡ t
to-fromΛ Infer (` x)       = refl
to-fromΛ Infer (t ∙ u)     = cong₂ _∙_ (to-fromΛ _ t) (to-fromΛ _ u)
to-fromΛ Infer (_ ∋ t)     = cong (_ ∋_) (to-fromΛ _ t)
to-fromΛ Check (ƛ t)       = cong ƛ_ (to-fromΛ _ t)
to-fromΛ Check (⇉ t by eq) = cong (⇉_by eq) (to-fromΛ _ t)