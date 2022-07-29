open import Prelude
  hiding (_▷_)

module Language.STLC.Abstract.Normal where

open import Language.STLC.Abstract.Term

private
  variable
--    Γ Δ : Cxt
    Γ Δ : Ty → Type
    A B : Ty
    M N L M′ N′ L′ : Tm Γ A

infix  3 _⊢ne_ _⊢nf_
infixr 9 ᵒ_ 

data _Normal  {Γ} : Tm Γ A → 𝓤₀ ̇ 
data _Neutral {Γ} : Tm Γ A → 𝓤₀ ̇  where
  `_
    : (x : Γ A)
    → (` x) Neutral 
  _·_
    : L       Neutral
    → M       Normal
    → (L · M) Neutral

data _Normal where
  ᵒ_
    : M Neutral
    → M Normal
  ƛ_
    : M     Normal
    → (ƛ M) Normal

soundness-normal  : M Normal  → ¬ (M -→ N)
soundness-neutral : M Neutral → ¬ (M -→ M′)

soundness-normal (ᵒ M↓) M→N       = soundness-neutral M↓ M→N
soundness-normal (ƛ M↓) (ξ-ƛ M→N) = soundness-normal M↓ M→N
soundness-neutral (` x) ()
soundness-neutral (L↓ · M↓) (ξ-·ₗ L→L′)   = soundness-neutral L↓ L→L′
soundness-neutral (L↓ · M↓) (ξ-·ᵣ M→M′)   = soundness-normal M↓ M→M′

completeness
  : (M : Tm Γ A) → (∀ N → ¬ (M -→ N))
  → M Normal
completeness (` x) M↛ = ᵒ ` x
completeness (ƛ M) ƛM↛ with completeness M M↛
  where M↛ : ∀ N → ¬ (M -→ N)
        M↛ N M→N = ƛM↛ (ƛ N) (ξ-ƛ M→N)
... | M↓ = ƛ M↓
completeness (M · N) MN↛ with completeness M M↛ | completeness N N↛
  where M↛ : ∀ M′ → ¬ (M -→ M′)
        M↛ M′ M↛ = MN↛ (M′ · N) (ξ-·ₗ M↛)
        N↛ : ∀ N′ → ¬ (N -→ N′)
        N↛ N′ N↛ = MN↛ (M · N′) (ξ-·ᵣ N↛)
... | ᵒ M↓ | N↓ = ᵒ (M↓ · N↓)
... | ƛ M↓ | N↓ = ⊥-elim (MN↛ _ β-ƛ· )

data _⊢nf_ (Γ : Ty → Type) : Ty → 𝓤₀ ̇ 
data _⊢ne_ Γ : Ty → 𝓤₀ ̇ where
  `_
    : (x : Γ A)
    → Γ ⊢ne A
  _·_
    : Γ ⊢ne A ⇒ B
    → Γ ⊢nf A
    → Γ ⊢ne B
data _⊢nf_ Γ where
  ᵒ_
    : Γ ⊢ne A
    → Γ ⊢nf A
  ƛ_
    : (Γ ▷ A) ⊢nf B
    → Γ ⊢nf A ⇒ B

↑ne_ : Γ ⊢ne A → Tm Γ A
↑nf_ : Γ ⊢nf A → Tm Γ A
↑ne (` x)     = ` x
↑ne (L · M)   = ↑ne L · (↑nf M)
↑nf (ᵒ M) = ↑ne M
↑nf (ƛ M) = ƛ (↑nf M)

↑nf-normal  : (M : Γ ⊢nf A) → (↑nf M) Normal
↑ne-neutral : (M : Γ ⊢ne A) → (↑ne M) Neutral

↑nf-normal (ᵒ M)        = ᵒ ↑ne-neutral M
↑nf-normal (ƛ M)        = ƛ ↑nf-normal M
↑ne-neutral (` x)       = ` x
↑ne-neutral (L · M)     = ↑ne-neutral L · ↑nf-normal M

↓ne : {M : Tm Γ A} → M Neutral → (Γ ⊢ne A)
↓nf : {M : Tm Γ A} → M Normal  → (Γ ⊢nf A)
↓ne (` x)     = ` x
↓ne (L · M)   = ↓ne L · ↓nf M
↓nf (ᵒ M)     = ᵒ ↓ne M
↓nf (ƛ N)     = ƛ ↓nf N

rename-nf : Ren Γ Δ → Δ ⊢nf A → Γ ⊢nf A
rename-ne : Ren Γ Δ → Δ ⊢ne A → Γ ⊢ne A
rename-ne σ (` x)       = ` σ x
rename-ne σ (M · N)     = rename-ne σ M · rename-nf σ N
rename-nf σ (ᵒ M)       = ᵒ rename-ne σ M
rename-nf σ (ƛ M)       = ƛ (rename-nf (ext σ) M)

