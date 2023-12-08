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
           → (Pre Syn r × Dec (∃[ A ] Γ ⊢ r ⦂ A)) ⊎ ¬ Pre Syn r
synthesise Γ r with decorate Syn r
... | no ¬p = inr ¬p
... | yes p with synthesise⇔ Γ p
... | no ¬At      = inl (p , no λ (_ , t) → ¬At (_ , completeness p t))
... | yes (_ , t) = inl (p , yes (_ , soundness t))

data Tri (P : Set) (Q : Set) (R : Set) : Set where
  only-p : P → ¬ Q → ¬ R → Tri P Q R
  only-q : Q → ¬ P → ¬ R → Tri P Q R
  only-r : R → ¬ P → ¬ Q → Tri P Q R

synthesise′
  : (Γ : Cxt 0) (r : Raw (length Γ))
  → Tri (Pre Syn r × ∃[ A ] Γ ⊢ r ⦂ A)
        (Pre Syn r × ¬ (∃[ A ] Γ ⊢ r ⦂ A))
        (¬ Pre Syn r)
synthesise′ Γ r with decorate Syn r
... | no ¬p = only-r ¬p (λ (p , _) → ¬p p) λ (p , _) → ¬p p 
... | yes p with synthesise⇔ Γ p
... | no ¬At      =
  only-q (p , λ (_ , t) → ¬At (_ , completeness p t)) (λ (_ , _ , At) → ¬At (_ , completeness p At)) (λ ¬p → ¬p p)
... | yes (_ , t) =
  only-p (p , _ , soundness t) (λ (_ , ¬At) → ¬At (_ , soundness t)) (λ ¬p → ¬p p)
