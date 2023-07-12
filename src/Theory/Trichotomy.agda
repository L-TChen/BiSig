import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

import Theory.ModeCorrectness.Signature as MC

module Theory.Trichotomy
  {SD : S.SigD} (D : B.SigD SD) (mc : MC.ModeCorrect SD D) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase D)
open import Syntax.Typed.Term     (erase D)
open import Syntax.BiTyped.Pre.Term      D

open import Theory.ModeDecoration            D
open import Theory.ModeCorrectness.Synthesis D mc
  renaming (synthesise to synthesise⇔)
open import Theory.Soundness                 D
open import Theory.Completeness              D

synthesise : (Γ : Cxt 0) (r : Raw (length Γ))
           → Dec (∃[ A ] Γ ⊢ r ⦂ A) ⊎ ¬ Pre Syn r
synthesise Γ r with decorate Syn r
... | no ¬p = inr ¬p
... | yes p with synthesise⇔ Γ p
... | no ¬At      = inl (no λ (_ , t) → ¬At (_ , completeness p t))
... | yes (_ , t) = inl (yes (_ , soundness t))
