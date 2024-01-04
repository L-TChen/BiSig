module Example.Computational where

open import Prelude

variable
  n : ℕ
  d : Mode

import Syntax.Simple.Signature as S

data ΛₜOp : Set where
  nat imp times sum T : ΛₜOp

instance

  decΛₜOp : DecEq ΛₜOp
  decΛₜOp = record { _≟_ = dec }
    where
      dec : (x y : ΛₜOp) → Dec (x ≡ y)
      dec nat   nat   = yes refl
      dec imp   imp   = yes refl
      dec times times = yes refl
      dec sum   sum   = yes refl
      dec T     T     = yes refl
      dec nat   imp   = no λ ()
      dec nat   times = no λ ()
      dec nat   sum   = no λ ()
      dec nat   T     = no λ ()
      dec imp   nat   = no λ ()
      dec imp   times = no λ ()
      dec imp   sum   = no λ ()
      dec imp   T     = no λ ()
      dec times nat   = no λ ()
      dec times imp   = no λ ()
      dec times sum   = no λ ()
      dec times T     = no λ ()
      dec sum   nat   = no λ ()
      dec sum   imp   = no λ ()
      dec sum   times = no λ ()
      dec sum   T     = no λ ()
      dec T     nat   = no λ ()
      dec T     imp   = no λ ()
      dec T     times = no λ ()
      dec T     sum   = no λ ()


ΛₜD : S.SigD
ΛₜD = S.sigd ΛₜOp λ where
  nat   → 0
  imp   → 2
  times → 2
  sum   → 2
  T     → 1

open import Syntax.Simple.Term ΛₜD
  using (`_; op)
  renaming (Tm to Λₜ)

open import Syntax.Context ΛₜD

variable
  A B C : Λₜ  0
  Γ Δ   : Cxt 0

infixr 8 _⊃_

pattern nat′    = op (nat , [])
pattern _⊃_ A B = op (imp , A ∷ B ∷ [])
pattern _×̇_ A B = op (times , A ∷ B ∷ [])
pattern _∔_ A B = op (sum , A ∷ B ∷ [])
pattern T′  A   = op (T , A ∷ [])

open import Syntax.BiTyped.Signature ΛₜD

data ΛOp : Set where
  `app `abs `z `s `ifz `pair `proj₁ `proj₂ `inj₁ `inj₂ `case `mu `let `ret `bind : ΛOp

-- this should be derived by datatype-generic programming
decΛOp : DecEq ΛOp
decΛOp = record { _≟_ = dec }
  where
    dec : ∀ x y → Dec (x ≡ y)
    dec `app   `app   = yes refl
    dec `abs   `abs   = yes refl
    dec `z     `z     = yes refl
    dec `s     `s     = yes refl
    dec `ifz   `ifz   = yes refl
    dec `pair  `pair  = yes refl
    dec `proj₁ `proj₁ = yes refl
    dec `proj₂ `proj₂ = yes refl
    dec `mu    `mu    = yes refl
    dec `let   `let   = yes refl
    dec `inj₁  `inj₁  = yes refl
    dec `inj₂  `inj₂  = yes refl
    dec `case  `case  = yes refl
    dec `ret   `ret   = yes refl
    dec `bind  `bind  = yes refl
    dec `app `abs     = no λ ()
    dec `app `z       = no λ ()
    dec `app `s       = no λ ()
    dec `app `ifz     = no λ ()
    dec `app `pair    = no λ ()
    dec `app `proj₁   = no λ ()
    dec `app `proj₂   = no λ ()
    dec `app `inj₁    = no λ ()
    dec `app `inj₂    = no λ ()
    dec `app `case    = no λ ()
    dec `app `mu      = no λ ()
    dec `app `let     = no λ ()
    dec `app `ret     = no λ ()
    dec `app `bind    = no λ ()
    dec `abs `app     = no λ ()
    dec `abs `z       = no λ ()
    dec `abs `s       = no λ ()
    dec `abs `ifz     = no λ ()
    dec `abs `pair    = no λ ()
    dec `abs `proj₁   = no λ ()
    dec `abs `proj₂   = no λ ()
    dec `abs `inj₁    = no λ ()
    dec `abs `inj₂    = no λ ()
    dec `abs `case    = no λ ()
    dec `abs `mu      = no λ ()
    dec `abs `let     = no λ ()
    dec `abs `ret     = no λ ()
    dec `abs `bind    = no λ ()
    dec `z   `app     = no λ ()
    dec `z   `abs     = no λ ()
    dec `z   `s       = no λ ()
    dec `z   `ifz     = no λ ()
    dec `z   `pair    = no λ ()
    dec `z   `proj₁   = no λ ()
    dec `z   `proj₂   = no λ ()
    dec `z   `inj₁    = no λ ()
    dec `z   `inj₂    = no λ ()
    dec `z   `case    = no λ ()
    dec `z   `mu      = no λ ()
    dec `z   `let     = no λ ()
    dec `z   `ret     = no λ ()
    dec `z   `bind    = no λ ()
    dec `s   `app     = no λ ()
    dec `s   `abs     = no λ ()
    dec `s   `z       = no λ ()
    dec `s   `ifz     = no λ ()
    dec `s   `pair    = no λ ()
    dec `s   `proj₁   = no λ ()
    dec `s   `proj₂   = no λ ()
    dec `s   `inj₁    = no λ ()
    dec `s   `inj₂    = no λ ()
    dec `s   `case    = no λ ()
    dec `s   `mu      = no λ ()
    dec `s   `let     = no λ ()
    dec `s   `ret     = no λ ()
    dec `s   `bind    = no λ ()
    dec `ifz `app     = no λ ()
    dec `ifz `abs     = no λ ()
    dec `ifz `z       = no λ ()
    dec `ifz `s       = no λ ()
    dec `ifz `pair    = no λ ()
    dec `ifz `proj₁   = no λ ()
    dec `ifz `proj₂   = no λ ()
    dec `ifz `inj₁    = no λ ()
    dec `ifz `inj₂    = no λ ()
    dec `ifz `case    = no λ ()
    dec `ifz `mu      = no λ ()
    dec `ifz `let     = no λ ()
    dec `ifz `ret     = no λ ()
    dec `ifz `bind    = no λ ()
    dec `pair `app    = no λ ()
    dec `pair `abs    = no λ ()
    dec `pair `z      = no λ ()
    dec `pair `s      = no λ ()
    dec `pair `ifz    = no λ ()
    dec `pair `proj₁  = no λ ()
    dec `pair `proj₂  = no λ ()
    dec `pair `inj₁   = no λ ()
    dec `pair `inj₂   = no λ ()
    dec `pair `case   = no λ ()
    dec `pair `mu     = no λ ()
    dec `pair `let    = no λ ()
    dec `pair `ret    = no λ ()
    dec `pair `bind   = no λ ()
    dec `proj₁ `app   = no λ ()
    dec `proj₁ `abs   = no λ ()
    dec `proj₁ `z     = no λ ()
    dec `proj₁ `s     = no λ ()
    dec `proj₁ `ifz   = no λ ()
    dec `proj₁ `pair  = no λ ()
    dec `proj₁ `proj₂ = no λ ()
    dec `proj₁ `inj₁  = no λ ()
    dec `proj₁ `inj₂  = no λ ()
    dec `proj₁ `case  = no λ ()
    dec `proj₁ `mu    = no λ ()
    dec `proj₁ `let   = no λ ()
    dec `proj₁ `ret   = no λ ()
    dec `proj₁ `bind  = no λ ()
    dec `proj₂ `app   = no λ ()
    dec `proj₂ `abs   = no λ ()
    dec `proj₂ `z     = no λ ()
    dec `proj₂ `s     = no λ ()
    dec `proj₂ `ifz   = no λ ()
    dec `proj₂ `pair  = no λ ()
    dec `proj₂ `proj₁ = no λ ()
    dec `proj₂ `inj₁  = no λ ()
    dec `proj₂ `inj₂  = no λ ()
    dec `proj₂ `case  = no λ ()
    dec `proj₂ `mu    = no λ ()
    dec `proj₂ `let   = no λ ()
    dec `proj₂ `ret   = no λ ()
    dec `proj₂ `bind  = no λ ()
    dec `inj₁ `app    = no λ ()
    dec `inj₁ `abs    = no λ ()
    dec `inj₁ `z      = no λ ()
    dec `inj₁ `s      = no λ ()
    dec `inj₁ `ifz    = no λ ()
    dec `inj₁ `pair   = no λ ()
    dec `inj₁ `proj₁  = no λ ()
    dec `inj₁ `proj₂  = no λ ()
    dec `inj₁ `inj₂   = no λ ()
    dec `inj₁ `case   = no λ ()
    dec `inj₁ `mu     = no λ ()
    dec `inj₁ `let    = no λ ()
    dec `inj₁ `ret    = no λ ()
    dec `inj₁ `bind   = no λ ()
    dec `inj₂ `app    = no λ ()
    dec `inj₂ `abs    = no λ ()
    dec `inj₂ `z      = no λ ()
    dec `inj₂ `s      = no λ ()
    dec `inj₂ `ifz    = no λ ()
    dec `inj₂ `pair   = no λ ()
    dec `inj₂ `proj₁  = no λ ()
    dec `inj₂ `proj₂  = no λ ()
    dec `inj₂ `inj₁   = no λ ()
    dec `inj₂ `case   = no λ ()
    dec `inj₂ `mu     = no λ ()
    dec `inj₂ `let    = no λ ()
    dec `inj₂ `ret    = no λ ()
    dec `inj₂ `bind   = no λ ()
    dec `case `app    = no λ ()
    dec `case `abs    = no λ ()
    dec `case `z      = no λ ()
    dec `case `s      = no λ ()
    dec `case `ifz    = no λ ()
    dec `case `pair   = no λ ()
    dec `case `proj₁  = no λ ()
    dec `case `proj₂  = no λ ()
    dec `case `inj₁   = no λ ()
    dec `case `inj₂   = no λ ()
    dec `case `mu     = no λ ()
    dec `case `let    = no λ ()
    dec `case `ret    = no λ ()
    dec `case `bind   = no λ ()
    dec `mu `app      = no λ ()
    dec `mu `abs      = no λ ()
    dec `mu `z        = no λ ()
    dec `mu `s        = no λ ()
    dec `mu `ifz      = no λ ()
    dec `mu `pair     = no λ ()
    dec `mu `proj₁    = no λ ()
    dec `mu `proj₂    = no λ ()
    dec `mu `inj₁     = no λ ()
    dec `mu `inj₂     = no λ ()
    dec `mu `case     = no λ ()
    dec `mu `let      = no λ ()
    dec `mu `ret      = no λ ()
    dec `mu `bind     = no λ ()
    dec `let `app     = no λ ()
    dec `let `abs     = no λ ()
    dec `let `z       = no λ ()
    dec `let `s       = no λ ()
    dec `let `ifz     = no λ ()
    dec `let `pair    = no λ ()
    dec `let `proj₁   = no λ ()
    dec `let `proj₂   = no λ ()
    dec `let `inj₁    = no λ ()
    dec `let `inj₂    = no λ ()
    dec `let `case    = no λ ()
    dec `let `mu      = no λ ()
    dec `let `ret     = no λ ()
    dec `let `bind    = no λ ()
    dec `ret `app     = no λ ()
    dec `ret `abs     = no λ ()
    dec `ret `z       = no λ ()
    dec `ret `s       = no λ ()
    dec `ret `ifz     = no λ ()
    dec `ret `pair    = no λ ()
    dec `ret `proj₁   = no λ ()
    dec `ret `proj₂   = no λ ()
    dec `ret `inj₁    = no λ ()
    dec `ret `inj₂    = no λ ()
    dec `ret `case    = no λ ()
    dec `ret `mu      = no λ ()
    dec `ret `let     = no λ ()
    dec `ret `bind    = no λ ()
    dec `bind `app    = no λ ()
    dec `bind `abs    = no λ ()
    dec `bind `z      = no λ ()
    dec `bind `s      = no λ ()
    dec `bind `ifz    = no λ ()
    dec `bind `pair   = no λ ()
    dec `bind `proj₁  = no λ ()
    dec `bind `proj₂  = no λ ()
    dec `bind `inj₁   = no λ ()
    dec `bind `inj₂   = no λ ()
    dec `bind `case   = no λ ()
    dec `bind `mu     = no λ ()
    dec `bind `let    = no λ ()
    dec `bind `ret    = no λ ()


PCF⟺D : SigD
PCF⟺D = record
  { Op    = ΛOp
  ; decOp = decΛOp
  ; ar    = λ { `app   → 2 ▷ ρ[ [] ⊢[ Chk ] ` 1 ]
                           ρ[ [] ⊢[ Syn ] ` 1 ⊃ ` 0 ] [] ⇒ ` 0
                    -- Γ ⊢ t : A → B    Γ ⊢ u : A
                    -------------------------------
                    -- Γ ⊢ t u ⇒ B

              ; `abs   → 2 ▷ ρ[ (` 1 ∷ []) ⊢[ Chk ] ` 0 ] [] ⇐ (` 1) ⊃ (` 0) 
                    -- Γ , x : A ⊢ t ⇐ B
                    ------------------------
                    -- Γ ⊢ λ x . t ⇐ A → B
              ; `z     → 0 ▷ [] ⇐ nat′
              ; `s     → 0 ▷ ρ[ [] ⊢[ Chk ] nat′ ] [] ⇐ nat′
              ; `ifz   → 1 ▷
                ρ[ [] ⊢[ Chk ] ` 0 ] ρ[ [] ⊢[ Chk ] ` 0 ] ρ[ [] ⊢[ Syn ] nat′ ] [] ⇐ ` 0
              ; `pair  → 2 ▷ ρ[ [] ⊢[ Chk ] ` 0 ] ρ[ [] ⊢[ Chk ] ` 1 ] [] ⇐ (` 1) ×̇ (` 0)
              ; `proj₁ → 2 ▷ ρ[ [] ⊢[ Syn ] (` 1) ×̇ (` 0) ] [] ⇒ ` 1 
              ; `proj₂ → 2 ▷ ρ[ [] ⊢[ Syn ] (` 1) ×̇ (` 0) ] [] ⇒ ` 0 
              ; `inj₁ → 2 ▷ ρ[ [] ⊢[ Chk ] ` 0 ] [] ⇐ (` 0) ∔ (` 1) 
              ; `inj₂ → 2 ▷ ρ[ [] ⊢[ Chk ] ` 1 ] [] ⇐ (` 0) ∔ (` 1) 
              ; `case → 3 ▷ ρ[ (` 0 ∷ []) ⊢[ Chk ] ` 2 ] ρ[ (` 1 ∷ []) ⊢[ Chk ] ` 2 ] ρ[ [] ⊢[ Syn ] (` 0) ∔ (` 1 )] [] ⇐ ` 2
              ; `mu    → 1 ▷ ρ[ (` 0 ∷ []) ⊢[ Chk ] ` 0 ] [] ⇐ ` 0
              ; `let   → 2 ▷ ρ[ (` 1 ∷ []) ⊢[ Chk ] ` 0 ] ρ[ [] ⊢[ Syn ] ` 1 ] [] ⇐ ` 0
              ; `ret   → 1 ▷ ρ[ [] ⊢[ Syn ] ` 0 ] [] ⇒ ` 0
              ; `bind  → 2 ▷ ρ[ (` 0 ∷ []) ⊢[ Syn ] T′ (` 1) ] ρ[ [] ⊢[ Syn ] T′ (` 0) ] [] ⇒ T′ (` 1)
              }
  }

open import Theory.ModeCorrectness.Signature    ΛₜD
open import Theory.ModeCorrectness.Decidability ΛₜD

mcPCF⟺D : ModeCorrect PCF⟺D
mcPCF⟺D `app   = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `app))
mcPCF⟺D `abs   = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `abs))
mcPCF⟺D `z     = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `z))
mcPCF⟺D `s     = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `s))
mcPCF⟺D `ifz   = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `ifz))
mcPCF⟺D `pair  = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `pair))
mcPCF⟺D `proj₁ = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `proj₁))
mcPCF⟺D `proj₂ = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `proj₂))
mcPCF⟺D `inj₁  = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `inj₁))
mcPCF⟺D `inj₂  = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `inj₂))
mcPCF⟺D `case  = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `case))
mcPCF⟺D `mu    = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `mu))
mcPCF⟺D `let   = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `let))
mcPCF⟺D `ret   = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `ret))
mcPCF⟺D `bind  = from-yes (ModeCorrectᶜ? (PCF⟺D .ar `bind))

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase PCF⟺D)

variable
  r s : Raw _

infixl 8 _·_
infixr 7 ƛ_

pattern _·_ r s = op (`app , s , r , _)
pattern ƛ_  r   = op (`abs , r , _)

S : Raw n
S = ƛ ƛ ƛ ` suc (suc zero) · ` zero · (` suc zero · ` zero)

open import Syntax.BiTyped.Term PCF⟺D

infixl 8 _·ᴮ_

_·ᴮ_ : Γ ⊢ r ⇒ (A ⊃ B)  →  Γ ⊢ s ⇐ A  →  Γ ⊢ (r · s) ⇒ B
t ·ᴮ u = op (refl , lookup (_ ∷ _ ∷ []) , refl , u , t , _)

ƛᴮ_ : (A ∷ Γ) ⊢ r ⇐ B  →  Γ ⊢ (ƛ r) ⇐ (A ⊃ B)
ƛᴮ t = op (refl , lookup (_ ∷ _ ∷ []) , refl , t , _)

⊢S : Γ ⊢ S ⇐ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
⊢S = ƛᴮ ƛᴮ ƛᴮ ((var (there (there (here refl))) refl ·ᴮ ((var (here refl) refl) ↑ refl) ·ᴮ
              ((var        (there (here refl))  refl ·ᴮ ((var (here refl) refl) ↑ refl)) ↑ refl)) ↑ refl)

open import Theory.Trichotomy PCF⟺D mcPCF⟺D

⊢S? : _  -- Normalise me!
⊢S? = synthesise [] (((nat′ ⊃ nat′ ⊃ nat′) ⊃ (nat′ ⊃ nat′) ⊃ nat′ ⊃ nat′) ∋ S)
