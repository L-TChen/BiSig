open import Prelude

import Syntax.Simple.Description as S

module Language.Soundness.Term {SD : S.Desc} where

open import Data.List.Membership.Propositional

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open import Syntax.Context

open import Syntax.Typed.Description    {SD} as T
open import Syntax.BiTyped.Description  {SD} as B

open import Syntax.Typed.Intrinsic.Functor    as T
open import Syntax.BiTyped.Intrinsic.Functor  as B

open import Syntax.Typed.Intrinsic.Term
open import Syntax.BiTyped.Intrinsic.Term
  renaming (Tm to BTm)

open import Language.Erasure.Description
open import Language.Soundness.Description

private variable
  m : Mode
  Ξ : ℕ
  A : T
  σ : Sub₀ Ξ
  Γ : Ctx T

module _ (BD : B.Desc) (TD : T.Desc) (s : Soundness BD TD) where mutual
  forget
    : BTm BD m A Γ
    → Tm  TD   A Γ
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op x)        = op (forgetMap _ _ s x)

  forgetMap
    : (Dᵇ : B.Desc) (Dᵗ : T.Desc)
    → Soundness Dᵇ Dᵗ
    → (B.⟦ Dᵇ ⟧ BTm BD) m A Γ
    → (T.⟦ Dᵗ ⟧ Tm  TD)   A Γ
  forgetMap Dᵇ Dᵗ s (D , i , p , σ , A=B , ts) = _ , s i , σ , A=B , forgetMapᵃˢ _ ts

  forgetMapᵃˢ
    : (D : B.ArgsD Ξ)
    → (B.⟦ D ⟧ᵃˢ BTm BD)        σ Γ
    → (T.⟦ eraseᵃˢ D ⟧ᵃˢ Tm TD) σ Γ
  forgetMapᵃˢ ι        _        = _
  forgetMapᵃˢ (ρ D Ds) (t , ts) = forgetMapᵃ D t , forgetMapᵃˢ Ds ts

  forgetMapᵃ
    : (D : B.ArgD Ξ)
    → (B.⟦ D ⟧ᵃ BTm BD)       σ Γ
    → (T.⟦ eraseᵃ D ⟧ᵃ Tm TD) σ Γ
  forgetMapᵃ (ι m B) t = forget t
  forgetMapᵃ (A ∙ D) t = forgetMapᵃ D t