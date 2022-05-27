open import Prelude

module Language.Inference where

open import Language.Type
open import Language.BiUntyped.Term as U
open import Language.BiSTLC.Term  as B

open import Cubical.Data.Maybe

postulate
  _≟ty_ : (A B : Ty) → Dec (A ≡ B)

_/_ : {X : Type}
  → (ρ : X → Ty) → Ty → X ⁺ → Ty
(ρ / A) Z     = A
(ρ / A) (S x) = ρ x

⦅_⦆ : {X : Type}
  → (X → Ty) → Ty → Type
⦅ ρ ⦆ A = Σ[ x ∈ _ ] ρ x ≡ A

lem : {X : Type} (ρ : X → Ty) {B : Ty}
  → ∀ A
  → (⦅ ρ ⦆ ▷ B) A
  → ⦅ ρ / B ⦆ A
lem ρ A Z           = Z , refl
lem ρ A (S (x , p)) = (S x) , p

-- N.B. we also need to know that `Ty` is a Set (in HoTT) followed by _≟ty_
-- so `ρ x ≡ A` is a proposition. Therefore, the preimage ∏ ⦅ ρ ⦆ is equivalent to X.

mutual
  check : {X : Type}
    → Λ X chk → (ρ : X → Ty) (A : Ty)
    → Maybe (Tm ⦅ ρ ⦆ chk A)
  check (ƛ t) ρ ι       = nothing
  check (ƛ t) ρ (A ⇒ B) with check t (ρ / A) B
  ... | nothing = nothing
  ... | just t′ = just (ƛ {!!}) -- attention
  -- Tm (⦅ ρ ⦆ ▷ A) chk B
  -- Tm ⦅ ρ / A ⦆   chk B
  check (conv t) ρ A with infer t ρ
  ... | nothing = nothing
  ... | just (B , t′) with B ≟ty A
  ... | yes p = just (conv p t′)
  ... | no ¬p = nothing 

  infer : ∀ {X : Type}
    → Λ X inf → (ρ : X → Ty)
    → Maybe (Σ[ A ∈ Ty ] Tm ⦅ ρ ⦆ inf A)
  infer (` x)   ρ = just (ρ x , ` (x , refl))
  infer (t ⦂ A) ρ with check t ρ A
  ... | nothing = nothing
  ... | just t  = just (A , t ⦂ A)
  infer (t · u)    ρ with infer t ρ
  ... | nothing = nothing
  ... | just (ι     , _) = nothing
  ... | just (A ⇒ B , t) with check u ρ A
  ... | nothing = nothing
  ... | just u  = just (B , t · u)

