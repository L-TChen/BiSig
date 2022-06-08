open import Prelude

import Syntax.Simple.Description  as S

module Language.Erasure.Type {SD : S.Desc} where

open import Syntax.Simple.Term as S
  using (`_; op)
  renaming (Sub to TSub)
open import Syntax.Simple.Unit
  using (⋆D; ⋆T; ⋆)

open import Syntax.BiTyped.Description as B
 
open import Syntax.Context

TExp = S.Tm
T    = S.Tm₀ SD

private variable
  m     : Mode
  Ξ     : ℕ
  σ     : Sub₀ {SD} Ξ
  Γ Δ   : Ctx T
  A B C : T

eraseCtx : Ctx T → Ctx ⋆T
eraseCtx ∅       = ∅
eraseCtx (A ∙ Γ) = ⋆ ∙ eraseCtx Γ

eraseIdx : A ∈ Γ → ⋆ ∈ eraseCtx Γ
eraseIdx zero    = zero
eraseIdx (suc x) = suc (eraseIdx x)

eraseSub : TSub SD Ξ 0 → TSub ⋆D Ξ 0
eraseSub []      = []
eraseSub (A ∷ Δ) = ⋆ ∷ eraseSub Δ

eraseᵃ : B.ArgD {SD} Ξ → B.ArgD {⋆D} Ξ
eraseᵃ (ι m B) = ι m ⋆
eraseᵃ (A ∙ Δ) = ⋆ ∙ eraseᵃ Δ

eraseᵃˢ : B.ArgsD {SD} Ξ → B.ArgsD {⋆D} Ξ
eraseᵃˢ ι        = ι
eraseᵃˢ (ρ D Ds) = ρ (eraseᵃ D) (eraseᵃˢ Ds)

eraseᶜ : B.ConD {SD} → B.ConD {⋆D}
eraseᶜ (ι Ξ m A D) = ι Ξ m ⋆ (eraseᵃˢ D)

erase : B.Desc {SD} → B.Desc {⋆D}
erase []       = []
erase (D ∷ Ds) = eraseᶜ D ∷ erase Ds

module _ {D : B.Desc} where mutual
  open import Syntax.BiTyped.Term      D
  open import Syntax.BiTyped.Unityped  (erase D) as U
    renaming (Tm to UTm)

  forget
    : Tm  m A Γ
    → UTm m ⋆ (eraseCtx Γ)
  forget (` x)      = U.` eraseIdx x
  forget (_ ∋ t)    = ⋆ U.∋ forget t
  forget (⇉ t by _) = U.⇉ forget t by refl
  forget (op t)     = U.op (forgetMap _ t) 

  forgetMap : (D : B.Desc)
    → (⟦ D ⟧       Tm ) m A Γ
    → (⟦ erase D ⟧ UTm) m ⋆ (eraseCtx Γ)
  forgetMap (D ∷ Ds) (inl t) = inl (forgetMapᶜ D t)
  forgetMap (D ∷ Ds) (inr u) = inr (forgetMap Ds u)

  forgetMapᶜ : (D : B.ConD)
    → (⟦ D        ⟧ᶜ Tm)  m A Γ
    → (⟦ eraseᶜ D ⟧ᶜ UTm) m ⋆ (eraseCtx Γ)
  forgetMapᶜ (ι Ξ m A D) (p , σ , q , ts) =
    p , eraseSub σ , refl , forgetMapᵃˢ D ts

  forgetMapᵃˢ : (D : B.ArgsD Ξ)
    → (⟦ D         ⟧ᵃˢ Tm) σ             Γ
    → (⟦ eraseᵃˢ D ⟧ᵃˢ UTm) (eraseSub σ) (eraseCtx Γ)
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ : (D : ArgD Ξ)
    → (⟦ D ⟧ᵃ        Tm)  σ            Γ
    → (⟦ eraseᵃ D ⟧ᵃ UTm) (eraseSub σ) (eraseCtx Γ)
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ Δ) t = forgetMapᵃ Δ t