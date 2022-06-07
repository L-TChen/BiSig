open import Prelude

open import Syntax.Simple.Description  as S
  using (⋆D)

module Language.Erasure.Type {SD : S.Desc} where

open import Syntax.Simple.Term as S
  using (`_; op; Sub)
open import Syntax.BiTyped.Description as B
 
open import Syntax.Context

T    = S.Tm₀ SD
TExp = S.Tm

⋆T = S.Tm₀ S.⋆D
⋆ : ⋆T
⋆ = S.op (inl tt)

private variable
  m     : Mode
  Ξ     : ℕ
  σ     : Sub SD Ξ 0
  Γ Δ   : Ctx T
  A B C : T

eraseCtx : Ctx T → Ctx ⋆T
eraseCtx ∅       = ∅
eraseCtx (A ∙ Γ) = ⋆ ∙ eraseCtx Γ

eraseIdx : A ∈ Γ → ⋆ ∈ (eraseCtx Γ)
eraseIdx zero    = zero
eraseIdx (suc x) = suc (eraseIdx x)

eraseTExp : TExp SD Ξ → TExp ⋆D Ξ
eraseTExp _      = op (inl tt)

eraseSub : Sub SD Ξ 0 → Sub ⋆D Ξ 0
eraseSub []      = []
eraseSub (A ∷ Δ) = ⋆ ∷ eraseSub Δ

eraseᵃ : B.ArgD Ξ → B.ArgD Ξ
eraseᵃ (ι m B) = ι m (eraseTExp B)
eraseᵃ (A ∙ Δ) = eraseTExp A ∙ eraseᵃ Δ

eraseᵃˢ : B.ArgsD Ξ → B.ArgsD Ξ
eraseᵃˢ ι        = ι
eraseᵃˢ (ρ D Ds) = ρ (eraseᵃ D) (eraseᵃˢ Ds)

-- T is non-empty
eraseᶜ : T → B.ConD {SD} → B.ConD {⋆D}
eraseᶜ A₀ (ι Ξ m A D) = ι Ξ m (eraseTExp A) (eraseᵃˢ D)

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

  forgetMapᶜ : (D′ : B.ConD)
    → (⟦ D′           ⟧ᶜ Tm D           ) m A Γ
    → (⟦ eraseᶜ A₀ D′ ⟧ᶜ Tm (erase A₀ D)) m ⋆ (eraseCtx Γ)
  forgetMapᶜ (ι Ξ m A D) (p , σ , q , ts) =
    p , eraseSub σ , refl , forgetMapᵃˢ D ts

  forgetMapᵃˢ : (D′ : B.ArgsD Ξ)
    → (⟦ D′ ⟧ᵃˢ Tm D) σ Γ
    → (⟦ eraseᵃˢ D′ ⟧ᵃˢ Tm (erase A₀ D)) (eraseSub σ) (eraseCtx Γ)
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ : (D′ : ArgD Ξ)
    → (⟦ D′ ⟧ᵃ Tm D) σ Γ
    → (⟦ eraseᵃ D′ ⟧ᵃ Tm (erase A₀ D)) (eraseSub σ) (eraseCtx Γ)
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ Δ) t = forgetMapᵃ Δ t