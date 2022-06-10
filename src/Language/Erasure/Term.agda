open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description as B

module Language.Erasure.Term {SD : S.Desc} {D : B.Desc {SD}} where

open import Syntax.Context
open import Syntax.Simple.Term SD 
  hiding (Tm) renaming (Tm₀ to T)
open import Syntax.Typed.Description   {SD} as T
open import Language.Erasure.Description {SD}

open import Syntax.BiTyped.Intrinsic.Functor as B
open import Syntax.Typed.Intrinsic.Functor   as T
open import Syntax.BiTyped.Intrinsic.Term  D
  renaming (Tm to BTm)
open import Syntax.Typed.Intrinsic.Term    (erase D)

open import Data.List.Membership.Propositional.Properties
private variable
  Ξ   : ℕ
  σ   : Sub₀ Ξ
  Γ Δ : Ctx T
  m   : Mode
  A B : T


mutual
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
  forgetMap Ds (ι Ξ m A D , i , p , σ , q , ts) =
    ι Ξ A (eraseᵃˢ D) , ∈-map⁺ eraseᶜ i , σ , q , forgetMapᵃˢ _ ts

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
