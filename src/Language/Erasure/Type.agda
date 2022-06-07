open import Prelude

import Syntax.Simple.Description  as S

module Language.Erasure.Type {SD : S.Desc} where

open import Syntax.Simple.Term
  hiding (Tm)
open S using (⋆D)

open import Syntax.BiTyped.Description as B
-- open import Syntax.BiTyped.Unityped    as U
 
open import Syntax.Context

T = Tm₀ SD

⋆T = Tm₀ ⋆D
⋆ : ⋆T
⋆ = op (inl tt)

private variable
  m     : Mode
  Γ Δ Ξ : Ctx T
  A B C : T

eraseCtx : Ctx T → Ctx ⋆T
eraseCtx ∅       = ∅
eraseCtx (A ∙ Γ) = ⋆ ∙ eraseCtx Γ

eraseIdx : _∈_ T A Γ → _∈_ ⋆T ⋆ (eraseCtx Γ)
eraseIdx zero    = zero
eraseIdx (suc x) = suc (eraseIdx x)

eraseTExp : TExp SD Ξ → TExp ⋆D (eraseCtx Ξ)
eraseTExp _      = op (inl tt)

eraseᵃ : B.ArgD Ξ → B.ArgD (eraseCtx Ξ)
eraseᵃ (ι m B) = ι m (eraseTExp B)
eraseᵃ (A ∙ Δ) = eraseTExp A ∙ eraseᵃ Δ

eraseᵃˢ : B.ArgsD Ξ → B.ArgsD (eraseCtx Ξ)
eraseᵃˢ ι        = ι
eraseᵃˢ (ρ D Ds) = ρ (eraseᵃ D) (eraseᵃˢ Ds)

-- T is non-empty
eraseᶜ : T → B.ConD Ξ → B.ConD (eraseCtx Ξ)
eraseᶜ _ (ι m A D) = ι m (eraseTExp A) (eraseᵃˢ D)
eraseᶜ ⋆ (σ D)     = σ λ
  where (op (inl (lift _))) → eraseᶜ ⋆ (D ⋆)

erase : T → B.Desc → B.Desc
erase _ []       = []
erase ⋆ (D ∷ Ds) = eraseᶜ ⋆ D ∷ erase ⋆ Ds

open import Syntax.BiTyped.Term  as B

module _ (A₀ : T) (D : B.Desc) where mutual
  forget
    : Tm D m       A Γ
    → Tm (erase A₀ D) m ⋆ (eraseCtx Γ)
  forget (` x)         = ` eraseIdx x
  forget (_ ∋ t)       = ⋆ ∋ forget t
  forget (⇉ t by _)    = ⇉ forget t by refl
  forget (op t)        = op (forgetMap _ t) 
  
  forgetMap : (D′ : B.Desc)
    → (⟦ D′ ⟧          Tm D           ) m A Γ
    → (⟦ erase A₀ D′ ⟧ Tm (erase A₀ D)) m ⋆ (eraseCtx Γ)
  forgetMap (D ∷ Ds) (inl t) = inl (forgetMapᶜ D t)
  forgetMap (D ∷ Ds) (inr u) = inr (forgetMap Ds u)

  forgetMapᶜ : (D′ : B.ConD Ξ)
    → (⟦ D′           ⟧ᶜ Tm D           ) m A Γ
    → (⟦ eraseᶜ A₀ D′ ⟧ᶜ Tm (erase A₀ D)) m ⋆ (eraseCtx Γ)
  forgetMapᶜ (ι m A D) (A=B , m=m′ , t) = refl , m=m′ , forgetMapᵃˢ D t
  forgetMapᶜ (σ D)     (A , t)  = ⋆ , {! forgetMapᶜ (D A) t  !} 

  forgetMapᵃˢ : (D′ : B.ArgsD Ξ)
    → (⟦ D′ ⟧ᵃˢ Tm D) Γ
    → (⟦ eraseᵃˢ D′ ⟧ᵃˢ Tm (erase A₀ D)) (eraseCtx Γ)
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ : (D′ : ArgD Ξ)
    → (⟦ D′ ⟧ᵃ Tm D) Γ
    → (⟦ eraseᵃ D′ ⟧ᵃ Tm (erase A₀ D)) (eraseCtx Γ)
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ Δ) t = forgetMapᵃ Δ t