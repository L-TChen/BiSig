open import Prelude

import Syntax.Simple.Description  as S

module Language.Erasure.Mode {SD : S.Desc} where

open import Syntax.Simple.Term SD 
  renaming (Tm₀ to T)

open import Syntax.Typed.Description  {SD} as T
open import Syntax.BiTyped.Description as B
 
open import Syntax.Context

private variable
  Ξ     : ℕ
  σ     : Sub Ξ 0
  Γ Δ   : Ctx T

eraseᵃ : B.ArgD Ξ → T.ArgD Ξ
eraseᵃ (ι m B)   = ⊢ B
eraseᵃ (A ∙ Δ) = A ∙ eraseᵃ Δ

eraseᵃˢ : B.ArgsD Ξ → T.ArgsD Ξ
eraseᵃˢ ι        = ι
eraseᵃˢ (ρ D Ds) = ρ (eraseᵃ D) (eraseᵃˢ Ds)

eraseᶜ : B.ConD {SD} → T.ConD
eraseᶜ (ι Ξ m A D) = ι Ξ A (eraseᵃˢ D)

erase : B.Desc → T.Desc
erase []       = []
erase (D ∷ Ds) = eraseᶜ D ∷ erase Ds

open import Syntax.Typed.Term    as T
open import Syntax.BiTyped.Term  as B

private variable
  m   : Mode
  A B : T

module _ {D : B.Desc} where mutual
  forget
    : B.Tm D m       A Γ
    → T.Tm (erase D) A Γ 
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op t)        = op (forgetMap _ t)

  forgetMap : ∀ D′ → (B.⟦ D′ ⟧ B.Tm D) m A Γ → (T.⟦ erase D′ ⟧ T.Tm (erase D)) A Γ
  forgetMap (D ∷ Ds) (inl t) = inl (forgetMapᶜ D t)
  forgetMap (D ∷ Ds) (inr u) = inr (forgetMap Ds u)

  forgetMapᶜ : (D′ : B.ConD)
    → (B.⟦ D′ ⟧ᶜ B.Tm D) m A Γ
    → (T.⟦ eraseᶜ D′ ⟧ᶜ T.Tm (erase D)) A Γ
  forgetMapᶜ (ι Ξ m A D) (p , σ , q , ts) = σ , q , forgetMapᵃˢ D ts

  forgetMapᵃˢ : (D′ : B.ArgsD Ξ)
    → (B.⟦ D′ ⟧ᵃˢ B.Tm D) σ Γ
    → (T.⟦ eraseᵃˢ D′ ⟧ᵃˢ T.Tm (erase D)) σ Γ
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ : (D′ : B.ArgD Ξ)
    → (B.⟦ D′ ⟧ᵃ B.Tm D) σ Γ
    → (T.⟦ eraseᵃ D′ ⟧ᵃ T.Tm (erase D)) σ Γ
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ Δ) t = forgetMapᵃ Δ t
