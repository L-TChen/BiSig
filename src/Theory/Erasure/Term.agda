open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description as B

module Theory.Erasure.Term {SD : S.Desc} {D : B.Desc {SD}} where

open import Syntax.Context
open import Syntax.Simple.Term SD 
  hiding () renaming (Tm to TExp; Tms to TExps; Sub to TSub)

open import Syntax.BiTyped.Intrinsic.Functor as B
open import Syntax.Typed.Intrinsic.Functor   as T
open import Syntax.BiTyped.Intrinsic.Term  D
  renaming (Tm to BTm)

open import Theory.Erasure.Description {SD}
open import Syntax.Typed.Intrinsic.Term    (erase D)

open import Data.List.Membership.Propositional.Properties

private variable
  n m Ξ : ℕ
  σ   : TSub n m
  A B : TExp n
  Γ Δ : Cxt n
  mod : Mode

mutual
  forget
    : BTm Ξ mod A Γ
    → Tm  Ξ     A Γ
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op (D , i , p , σ , q , ts)) =
    op (eraseᶜ D , ∈-map⁺ eraseᶜ i , σ , q , forgetMap _ ts)

  forgetMap : (D : B.ArgsD n)
    → (B.⟦ D         ⟧ᵃˢ BTm Ξ) σ Γ
    → (T.⟦ eraseᵃˢ D ⟧ᵃˢ Tm  Ξ)  σ Γ
  forgetMap ∅        _                   = _
  forgetMap (Θ ⊢[ mod ] C ∙ Ds) (t , ts) =
    forgetMapᵃ Θ t , forgetMap Ds ts

  forgetMapᵃ : (Θ : TExps n)
    → (B.⟦ Θ ⟧ᵃ BTm Ξ mod A) σ Γ
    → (T.⟦ Θ ⟧ᵃ Tm  Ξ     A) σ Γ
  forgetMapᵃ ∅       t = forget t
  forgetMapᵃ (A ∙ Θ) t = forgetMapᵃ Θ t
