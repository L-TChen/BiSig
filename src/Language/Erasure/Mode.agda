open import Prelude

import Syntax.Simple.Description  as S

module Language.Erasure.Mode {SD : S.Desc} where

open import Syntax.Simple.Term SD 
  hiding (Tm) renaming (Tm₀ to T)

open import Syntax.Typed.Description   {SD} as T
open import Syntax.BiTyped.Description {SD} as B
 
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

eraseᶜ : B.ConD → T.ConD
eraseᶜ (ι Ξ m A D) = ι Ξ A (eraseᵃˢ D)

erase : B.Desc → T.Desc
erase []       = []
erase (D ∷ Ds) = eraseᶜ D ∷ erase Ds


module _ {D : B.Desc} where mutual
  private variable
    m   : Mode
    A B : T
  open import Syntax.BiTyped.Intrinsic.Functor         as B
  open import Syntax.BiTyped.Intrinsic.Term  D
    renaming (Tm to BTm)
  open import Syntax.Typed.Intrinsic.Functor           as T
  open import Syntax.Typed.Intrinsic.Term    (erase D)

  forget
    : BTm m A Γ
    → Tm    A Γ 
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op t)        = op (forgetMap _ t)

  forgetMap : ∀ D
    → (B.⟦ D       ⟧ BTm) m A Γ
    → (T.⟦ erase D ⟧ Tm)    A Γ
  forgetMap (ι Ξ m A D ∷ Ds) (inl (p , σ , q , ts)) = inl (σ , q , forgetMapᵃˢ D ts)
  forgetMap (D ∷ Ds) (inr u) = inr (forgetMap Ds u)
  
  forgetMapᵃˢ : (D : B.ArgsD Ξ)
    → (B.⟦ D         ⟧ᵃˢ BTm) σ Γ
    → (T.⟦ eraseᵃˢ D ⟧ᵃˢ Tm)  σ Γ
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ : (D : B.ArgD Ξ)
    → (B.⟦ D ⟧ᵃ        BTm) σ Γ
    → (T.⟦ eraseᵃ D ⟧ᵃ Tm)  σ Γ
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ Δ) t = forgetMapᵃ Δ t
