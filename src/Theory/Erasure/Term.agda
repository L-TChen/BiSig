{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Erasure.Term {SD : S.Desc} {D : B.Desc SD} where

open import Syntax.Context SD
open import Syntax.Simple  SD

open B SD

open import Theory.Erasure.Description {SD}

private variable
  Θ Ξ : ℕ
  ρ   : TSub Ξ Θ
  A B : TExp Θ
  Γ Δ : Cxt  Θ
  d   : Mode

module Raw (Id : Set) where mutual
  open import Syntax.BiTyped.Raw.Functor SD Id as BF
  open import Syntax.Typed.Raw.Functor   SD Id as TF

  open import Syntax.BiTyped.Raw.Term  Id D
    renaming (Raw to BiRaw)
  open import Syntax.Typed.Raw.Term    Id (erase D)

  forget
    : BiRaw Θ d
    → Raw   Θ
  forget (` x)             = ` x
  forget (t ⦂ A)           = forget t ⦂ A
  forget (t ↑)             = forget t
  forget (op (i , _ , ts)) = op (i , forgetⁿ _ ts)

  forgetⁿ
    : (D : ArgsD Ξ)
    → BF.⟦ D         ⟧ᵃˢ (BiRaw Θ)
    → TF.⟦ eraseᵃˢ D ⟧ᵃˢ (Raw Θ)
  forgetⁿ []                _        = _
  forgetⁿ (Δ ⊢[ d ] _ ∷ Ds) (t , ts) = forgetᵃ Δ t , forgetⁿ Ds ts

  forgetᵃ
    : (Δ : TExps Ξ)
    → BF.⟦ Δ ⟧ᵃ (BiRaw Θ d)
    → TF.⟦ Δ ⟧ᵃ (Raw Θ)
  forgetᵃ []      t       = forget t
  forgetᵃ (_ ∷ Δ) (x , t) = x , forgetᵃ Δ t

module Intrinsic where mutual
  open import Syntax.BiTyped.Intrinsic.Functor as B
  open import Syntax.Typed.Intrinsic.Functor   as T
  open import Syntax.BiTyped.Intrinsic.Term  D
    renaming (Tm to BiTm)
  open import Syntax.Typed.Intrinsic.Term    (erase D)

  forget
    : BiTm Θ d A Γ
    → Tm   Θ    A Γ
  forget (` x)         = ` x
  forget (_ ∋ t)       = forget t
  forget (⇉ t by refl) = forget t
  forget (op (i , p , σ , q , ts)) =
    op (i , σ , q , forgetMap _ ts)

  forgetMap : (D : ArgsD Ξ)
    → B.⟦ D         ⟧ᵃˢ (BiTm Θ) ρ Γ
    → T.⟦ eraseᵃˢ D ⟧ᵃˢ (Tm  Θ) ρ Γ
  forgetMap []     _                   = _
  forgetMap (Δ ⊢[ d ] B ∷ Ds) (t , ts) =
    forgetMapᵃ Δ t , forgetMap Ds ts 

  forgetMapᵃ : (Δ : TExps Ξ)
    → B.⟦ Δ ⟧ᵃ (BiTm Θ d A) ρ Γ
    → T.⟦ Δ ⟧ᵃ (Tm  Θ   A) ρ Γ
  forgetMapᵃ []      t = forget t
  forgetMapᵃ (A ∷ Δ) t = forgetMapᵃ Δ t
