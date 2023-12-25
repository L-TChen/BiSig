module Example.STLC where

open import Prelude
  hiding (_↣_)

variable
  n : ℕ
  d : Mode

data ΛₜOp : Set where base imp : ΛₜOp

instance

  decΛₜOp : DecEq ΛₜOp
  decΛₜOp = record { _≟_ = dec }
    where
      dec : (x y : ΛₜOp) → Dec (x ≡ y)
      dec base base = yes refl
      dec base imp  = no λ ()
      dec imp  base = no λ ()
      dec imp  imp  = yes refl

import Syntax.Simple.Signature as S

ΛₜD : S.SigD
ΛₜD = S.sigd ΛₜOp λ where base → 0; imp → 2

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

infixr 8 _⊃_

pattern b       = op (base , [])
pattern _⊃_ A B = op (imp , A ∷ B ∷ [])

open import Syntax.BiTyped.Signature ΛₜD

data ΛOp : Set where
  `app `abs : ΛOp

instance 
  decΛOp : DecEq ΛOp
  decΛOp = record { _≟_ = dec }
    where
      dec : ∀ x y → Dec (x ≡ y)
      dec `app `app = yes refl
      dec `app `abs = no λ ()
      dec `abs `app = no λ ()
      dec `abs `abs = yes refl

Λ⇔D : SigD
Λ⇔D .Op = ΛOp
Λ⇔D .ar = λ where
  `app → 2 ▷ ρ[ [] ⊢[ Chk ] ` 1 ]
                         ρ[ [] ⊢[ Syn ] ` 1 ⊃ ` 0 ] [] ⇒ ` 0
                  -- Γ ⊢ t : A → B    Γ ⊢ u : A
                  -------------------------------
                  -- Γ ⊢ t u ⇒ B

  `abs → 2 ▷ ρ[ (` 1 ∷ []) ⊢[ Chk ] ` 0 ] [] ⇐ (` 1) ⊃ (` 0) 
                  -- Γ , x : A ⊢ t ⇐ B
                  ------------------------
                  -- Γ ⊢ λ x . t ⇐ A → B

open import Theory.ModeCorrectness.Signature    ΛₜD
open import Theory.ModeCorrectness.Decidability ΛₜD

mcΛ⇔D : ModeCorrect Λ⇔D
mcΛ⇔D `app = from-yes (ModeCorrectᶜ? (Λ⇔D .ar `app))
mcΛ⇔D `abs = from-yes (ModeCorrectᶜ? (Λ⇔D .ar `abs))

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase Λ⇔D)

variable
  r s : Raw _

infixl 8 _·_
infixr 7 ƛ_

pattern _·_ r s = op (`app , s , r , _)
pattern ƛ_  r   = op (`abs , r , _)

S : Raw n
S = ƛ ƛ ƛ ` suc (suc zero) · ` zero · (` suc zero · ` zero)

open import Syntax.BiTyped.Term Λ⇔D

infixl 8 _·ᴮ_
-- infixr 7 ƛᴮ_

_·ᴮ_ : Γ ⊢ r ⇒ (A ⊃ B)  →  Γ ⊢ s ⇐ A  →  Γ ⊢ (r · s) ⇒ B
t ·ᴮ u = op (refl , lookup (_ ∷ _ ∷ []) , refl , u , t , _)

ƛᴮ_ : (A ∷ Γ) ⊢ r ⇐ B  →  Γ ⊢ (ƛ r) ⇐ (A ⊃ B)
ƛᴮ t = op (refl , lookup (_ ∷ _ ∷ []) , refl , t , _)

⊢S : Γ ⊢ S ⇐ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
⊢S = ƛᴮ ƛᴮ ƛᴮ ((var (there (there (here refl))) refl ·ᴮ ((var (here refl) refl) ↑ refl) ·ᴮ
              ((var        (there (here refl))  refl ·ᴮ ((var (here refl) refl) ↑ refl)) ↑ refl)) ↑ refl)

open import Theory.Trichotomy Λ⇔D mcΛ⇔D

⊢S? : _  -- Normalise me!
⊢S? = synthesise [] (((b ⊃ b ⊃ b) ⊃ (b ⊃ b) ⊃ b ⊃ b) ∋ S)
