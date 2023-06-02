{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Ontologisation.Term {SD : S.Desc} (D : B.Desc SD) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.NamedContext SD Id

open import Syntax.BiTyped.Raw.Functor SD Id   as R
open import Syntax.BiTyped.Raw.Term       Id D

open import Syntax.BiTyped.Extrinsic.Functor SD Id   as E
open import Syntax.BiTyped.Extrinsic.Term       Id D

open import Syntax.BiTyped.Intrinsic.Functor {SD} as I
open import Syntax.BiTyped.Intrinsic.Term         D

open import Theory.Ontologisation.Context          Id

open B SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  ρ   : TSub Ξ Θ
  A B : TExp Θ
  Γ   : Cxt Θ
  t u : Raw Θ d

mutual
  ∥_∥⇒
    : Γ ⊢ t ⇒ A
    → Tm⇒ Θ A ∥ Γ ∥cxt
  ∥ ⊢` x ∥⇒ = ` ∥ x ∥∈
  ∥ ⊢⦂ t ∥⇒ = _ ∋ ∥ t ∥⇐
  ∥ ⊢op (i , q , t) (σ , B=A , p) ∥⇒ =
    op (i , q , σ , B=A , ∥-∥map _ p)

  ∥_∥⇐
    : Γ ⊢ t ⇐ A
    → Tm⇐ Θ A ∥ Γ ∥cxt
  ∥ ⊢↑ p t ∥⇐ = ∥ t ∥⇒ ↑by p
  ∥ ⊢op (i , q , t) (σ , B=A , p) ∥⇐ =
    op (i , q , σ , B=A , ∥-∥map _ p)

  ∥-∥map : (D : ArgsD Ξ)
    → {t : R.⟦ D ⟧ᵃˢ (Raw Θ)}
    → E.⟦ D ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ Γ t
    → I.⟦ D ⟧ᵃˢ (Tm  Θ)    ρ ∥ Γ ∥cxt
  ∥-∥map []                _        = tt
  ∥-∥map (Δ ⊢[ d ] _ ∷ Ds) (p , ps) = ∥-∥mapᵃ Δ p , ∥-∥map Ds ps

  ∥-∥mapᵃ : (Δ : TExps Ξ)
    → {t : R.⟦ Δ ⟧ᵃ (Raw Θ d)}
    → E.⟦ Δ ⟧ᵃ (Raw Θ)    (⊢⇆ d A) ρ Γ t
    → I.⟦ Δ ⟧ᵃ (Tm Θ d A)          ρ ∥ Γ ∥cxt
  ∥-∥mapᵃ {d = Chk} []      p = ∥ p ∥⇐
  ∥-∥mapᵃ {d = Syn} []      p = ∥ p ∥⇒
  ∥-∥mapᵃ           (A ∷ Θ) p = ∥-∥mapᵃ Θ p
