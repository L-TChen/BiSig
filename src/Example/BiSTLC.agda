open import Prelude
  hiding (_↣_)

module Example.BiSTLC where

open import Syntax.Simple.Description as S

ΛₜD : S.Desc
ΛₜD = 0 ∷ 2 ∷ []

open import Syntax.Simple.Term ΛₜD
  using (`_)
  renaming (Tm₀ to Λₜ ; op to top)
open import Syntax.Context
  renaming (_≟_ to _≟ctx_)

infixr 10 _↣_
pattern _↣_ A B = top (inr (inl (A , B , _)))
{-
data Λₜ : Set where
  ι   :              Λₜ
  _↣_ : (A B : Λₜ) → Λₜ
-}

private variable
  T     : Set
  A B C : Λₜ
  Γ Δ   : Ctx T
 
open import Syntax.BiTyped.Description {ΛₜD} as T

ΛₒD : T.Desc
ΛₒD =
  2 ▷ ρ[ ⇉ (` # 0) ↣ (` # 1) ] ρ[ ⇇ ` # 0 ] ι ⇉ ` # 1 ∷
  2 ▷ ρ[ ` # 0 ∙ ⇇ ` # 1 ] ι                  ⇇ (` # 0) ↣ (` # 1) ∷
  []
 
open import Syntax.BiTyped.Term ΛₒD

pattern _∙′_ t u = op (inl (refl , (_ ∷ _ ∷  []) , refl , t , u , _))
pattern ƛ′_  t   = op (inr (inl (refl , (_ ∷ _ ∷ []) , refl , t , _)))

mutual
  data Λ⇉ : Λₜ → Ctx Λₜ → Set where
    `_ : _∈_ ⇒ Λ⇉
    _∙_
      : (t : Λ⇉ (A ↣ B) Γ) (u : Λ⇇ A Γ)
      → Λ⇉ B Γ
    _∋_
      : (A : Λₜ) (t : Λ⇇ A Γ)
      → Λ⇉ A Γ

  data Λ⇇ : Λₜ → Ctx Λₜ → Set where
    ƛ_ 
      : (t : Λ⇇ B (A ∙ Γ))
      → Λ⇇ (A ↣ B) Γ
    ⇉_by_
      : (t : Λ⇉ A Γ) (eq : A ≡ B)
      → Λ⇇ B Γ

Λ : Fam₀
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

open import Syntax.Simple.Unit
mutual
  data UΛ⇉ : ⋆T → Ctx ⋆T → Set where
    `_ : _∈_ ⇒ UΛ⇉
    _∙_
      : (t : UΛ⇉ ⋆ Γ) (u : UΛ⇇ ⋆ Γ)
      → UΛ⇉ ⋆ Γ
    _∋_
      : (A : Λₜ) (t : UΛ⇇ ⋆ Γ)
      → UΛ⇉ ⋆ Γ

  data UΛ⇇ : ⋆T → Ctx ⋆T → Set where
    ƛ_ 
      : (t : UΛ⇇ ⋆ (⋆ ∙ Γ))
      → UΛ⇇ ⋆ Γ
    ↑_
      : (t : UΛ⇉ ⋆ Γ)
      → UΛ⇇ ⋆ Γ

UΛ : Mode → ⋆T → Ctx ⋆T → Set
UΛ Check = UΛ⇇
UΛ Infer = UΛ⇉

eraseCtx : Ctx Λₜ → Ctx ⋆T
eraseCtx ∅       = ∅
eraseCtx (A ∙ Γ) = ⋆ ∙ eraseCtx Γ

eraseIdx : A ∈ Γ → ⋆ ∈ eraseCtx Γ
eraseIdx zero    = zero
eraseIdx (suc x) = suc (eraseIdx x)

erase : {m : Mode} → Λ m A Γ → UΛ m ⋆ (eraseCtx Γ)
erase {m = Check} (ƛ t)       = ƛ erase t
erase {m = Check} (⇉ t by eq) = ↑ erase t
erase {m = Infer} (` x)       = ` eraseIdx x
erase {m = Infer} (t ∙ u)     = erase t
erase {m = Infer} (A ∋ t)     = A ∋ erase t

lookup : (Γ : Ctx Λₜ) (x : ⋆ ∈ eraseCtx Γ)
  → Σ[ A ∈ Λₜ ] Σ[ x′ ∈ A ∈ Γ ] eraseIdx x′ ≡ x
lookup (A ∙ Γ′) zero    = A , zero , refl
lookup (A ∙ Γ′) (suc x) with lookup Γ′ x 
... | (B , y , refl) = B , suc y , refl

open import Syntax.Simple.Operation {ΛₜD}
  renaming (_≟_ to _≟T_)

mutual
  infer : (Γ : Ctx Λₜ) (t : UΛ⇉ ⋆ (eraseCtx Γ)) 
    → Dec (Σ[ A ∈ Λₜ ] Σ[ t′ ∈ Λ⇉ A Γ ] erase t′ ≡ t)
  infer Γ (` x) with lookup Γ x 
  ... | (A , x , refl) = yes (A , ` x , refl) 
  infer Γ (t ∙ u) with infer Γ t
  ... | no ¬p               = no λ where (A , t′ , p) → ¬p (A , t′ , {!   !})
  ... | yes (top (inl      _)            , t′ , refl) = no λ where (A , t′ , p) → {!   !}
  ... | yes (top (inr (inl (A , B , _))) , t′ , refl) = {!   !}
  infer Γ (A ∋ t) with check A Γ t 
  ... | yes (t′ , refl) = yes (A , A ∋ t′ , refl)
  ... | no ¬p = no λ where (A , t′ , q) → {!   !}

  check : (A : Λₜ) (Γ : Ctx Λₜ) (t : UΛ⇇ ⋆ (eraseCtx Γ)) 
    → Dec (Σ[ t′ ∈ Λ⇇ A Γ ] erase t′ ≡ t)
  check (top (inl _))                 Γ (ƛ t) = {!   !}
  check (top (inl _))                 Γ (↑ t) = {!   !}
  check (top (inr (inl (x , y , _)))) Γ t = {!   !}