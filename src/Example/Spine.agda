module Example.Spine where

open import Prelude
  hiding (_↣_)

variable
  m n : ℕ
  d   : Mode

import Syntax.Simple.Signature as S

data ΛₜOp : Set where
  base imp : ΛₜOp

instance

  decΛₜOp : DecEq ΛₜOp
  (decΛₜOp .DecEq._≟_) base base = yes refl
  (decΛₜOp .DecEq._≟_) imp  imp  = yes refl
  (decΛₜOp .DecEq._≟_) base imp  = no λ ()
  (decΛₜOp .DecEq._≟_) imp  base = no λ ()

ΛₜD : S.SigD
ΛₜD = S.sigd ΛₜOp λ { base → 0; imp → 2 }

open import Syntax.Simple.Term ΛₜD
  using (`_; op)
  renaming (Tm to Λₜ)

open import Syntax.Context ΛₜD

variable
  A B C : Λₜ  0
  Γ Δ   : Cxt 0

infixr 8 _↣_

pattern b       = op (base , [])
pattern _↣_ A B = op (imp , A ∷ B ∷ [])

open import Syntax.BiTyped.Signature ΛₜD

data SpineOp : Set where
  `abs :     SpineOp
  `app : ℕ → SpineOp

Π : Vec (Λₜ m) n → Λₜ m → Λₜ m
Π []       B = B
Π (A ∷ As) B = A ↣ Π As B

decSpineOp : DecEq SpineOp
decSpineOp = record { _≟_ = dec }
  where
    dec : ∀ x y → Dec (x ≡ y)
    dec  `abs     `abs    = yes refl
    dec  `abs    (`app n) = no λ ()
    dec (`app m)  `abs    = no λ ()
    dec (`app m) (`app n) with m ≟ n
    ... | yes refl = yes refl
    ... | no  m≢n  = no λ { refl → m≢n refl }

argTypes : Vec (Λₜ (suc n)) n
argTypes = V.tabulate (`_ ∘ suc)

chkArgs : Vec (Λₜ m) n → ArgsD m → ArgsD m
chkArgs []       D = D
chkArgs (A ∷ As) D = ρ[ [] ⊢[ Chk ] A ] chkArgs As D

SpineD : SigD
SpineD = record
  { Op    = SpineOp
  ; decOp = decSpineOp
  ; ar    = λ { `abs → 2 ▷ ρ[ (` 1 ∷ []) ⊢[ Chk ] ` 0 ] [] ⇐ (` 1) ↣ (` 0)
                    -- Γ , x : A ⊢ t ⇐ B
                    ------------------------
                    -- Γ ⊢ λ x . t ⇐ A → B
              ; (`app n) → suc n ▷ (chkArgs argTypes
                                   (ρ[ [] ⊢[ Syn ] Π argTypes (` 0) ] [])) ⇒ ` 0 } }
                    -- Γ ⊢ t ⇒ A₁ → ... → Aₙ → A    Γ ⊢ u₁ ⇐ A₁    ...    Γ ⊢ uₙ ⇐ Aₙ
                    -------------------------------------------------------------------
                    -- Γ ⊢ t u₁ ... uₙ ⇒ A

open import Theory.ModeCorrectness.Signature    ΛₜD
open import Theory.ModeCorrectness.Decidability ΛₜD

-- mcSpineD : ModeCorrect SpineD
-- mcSpineD `abs     = from-yes (ModeCorrectᶜ? (SpineD .ar `abs))
-- mcSpineD (`app n) = {!   !}