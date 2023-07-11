import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

import Theory.ModeCorrectness.Description as MC

module Theory.Trichotomy
  {SD : S.Desc} (D : B.Desc SD) (mc : MC.ModeCorrect SD D) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Theory.Erasure

open import Syntax.Typed.Raw.Term (erase D)
open import Syntax.Typed.Term     (erase D)
open import Syntax.BiTyped.Pre.Term      D

open import Theory.ModePreprocessing         D
open import Theory.ModeCorrectness.Synthesis D mc
  renaming (synthesise to synthesise⇔)
open import Theory.Soundness                 D
open import Theory.Completeness              D

synthesise : (Γ : Cxt 0) (r : Raw (length Γ))
           → Dec (∃[ A ] Γ ⊢ r ⦂ A) ⊎ ¬ Pre Syn r
synthesise Γ r with preprocess Syn r
... | no ¬p = inr ¬p
... | yes p with synthesise⇔ Γ p
... | no ¬At      = inl (no λ (_ , t) → ¬At (_ , completeness p t))
... | yes (_ , t) = inl (yes (_ , soundness t))
