open import Prelude

import Syntax.Simple.Description as S

module Theory.Soundness {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context     SD

open import Syntax.Typed.Description    {SD} as T
open import Syntax.BiTyped.Description  {SD} as B

open import Syntax.Typed.Intrinsic.Functor    as T
open import Syntax.BiTyped.Intrinsic.Functor  as B

open import Syntax.Typed.Intrinsic.Term
open import Syntax.BiTyped.Intrinsic.Term
  renaming (Tm to BTm)

open import Theory.Erasure.Description

private variable
  mod   : Mode
  n m   : ℕ
  A B C : TExp n
  σ     : TSub n m
  Γ     : Cxt n

-- A bidirectional typing is sound with respect to a base typing
-- if every bidirectional typing rule corresonds to a base typing rule.
Soundness : B.Desc → T.Desc → Set
Soundness BDs TDs = ∀ {D} → D ∈ BDs → eraseᶜ D ∈ TDs

module _ (BD : B.Desc) (TD : T.Desc) (s : Soundness BD TD) where mutual
  forget
    : BTm BD m mod A Γ
    → Tm  TD m A Γ
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op (_ , i , _ , σ , A=B , ts)) =
    op (_ , s i , σ , A=B , forgetMap _ ts)
  -- p is ignored.

  forgetMap
    : (D : B.ArgsD n)
    → B.⟦ D ⟧ᵃˢ         (BTm BD m) σ Γ
    → T.⟦ eraseᵃˢ D ⟧ᵃˢ (Tm TD m)  σ Γ
  forgetMap ∅                 _        = _
  forgetMap (Θ ⊢[ m ] B ∙ Ds) (t , ts) = forgetMapᵃ Θ t , forgetMap Ds ts
 
  forgetMapᵃ
    : (Θ : TExps n)
    → B.⟦ Θ ⟧ᵃ (BTm BD m mod A) σ Γ
    → T.⟦ Θ ⟧ᵃ (Tm  TD m  A)    σ Γ
  forgetMapᵃ ∅       t = forget t
  forgetMapᵃ (_ ∙ Θ) t = forgetMapᵃ Θ t
