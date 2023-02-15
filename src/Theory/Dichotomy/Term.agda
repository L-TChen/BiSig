{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Theory.Dichotomy.Term {SD : S.Desc} (D : Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.NamedContext SD Id

open import Syntax.BiTyped.Raw.Functor {SD} Id   as R
open import Syntax.BiTyped.Raw.Term         Id D

open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D as E
open import Syntax.BiTyped.Extrinsic.Term         Id D

open import Syntax.BiTyped.Intrinsic.Functor {SD}      as I
open import Syntax.BiTyped.Intrinsic.Term            D

open import Theory.Dichotomy.Context              Id

private variable
  mod   : Mode
  n m l : ℕ
  σ     : TSub n m
  A B C : TExp n
  x y   : Id
  Γ     : Cxt n
  t u   : Raw m mod

mutual
  ∥_∥⇉
    : Γ ⊢ t ⇉ A
    → Tm⇉ m A ∥ Γ ∥ctx
  ∥ ⊢` x     ∥⇉ = ` ∥ x ∥∈
  ∥ ⊢⦂ t     ∥⇉ = _ ∋ ∥ t ∥⇇
  ∥ ⊢op (ι Infer B D , i , q , t) (σ , B=A , p) ∥⇉ =
    op (_ , i , q , σ , B=A , ∥-∥map D p)

  ∥_∥⇇
    : Γ ⊢ t ⇇ A
    → Tm⇇ m A ∥ Γ ∥ctx
  ∥ ⊢⇉ t  p ∥⇇ = ⇉ ∥ t ∥⇉ by p
  ∥ ⊢op (ι Check B D , i , q , t) (σ , B=A , p) ∥⇇ =
    op (_ , i , q , σ , B=A , ∥-∥map D p)

  ∥-∥map : (D : ArgsD n)
    → {t : R.⟦ D ⟧ᵃˢ (Raw m)}
    → E.⟦ D ⟧ᵃˢ (Raw m) ⊢⇄ σ Γ t
    → (I.⟦ D ⟧ᵃˢ (Tm  m))      σ ∥ Γ ∥ctx 
  ∥-∥map ∅                 _        = tt
  ∥-∥map (Θ ⊢[ m ] B ∙ Ds) (p , ps) = ∥-∥mapᵃ Θ p , ∥-∥map Ds ps

  ∥-∥mapᵃ : (Θ : TExps n)
    → {t : R.⟦ Θ ⟧ᵃ (Raw m mod)}
    → E.⟦ Θ ⟧ᵃ (Raw m) (⊢⇄ mod A) σ Γ t
    → I.⟦ Θ ⟧ᵃ (Tm m mod A) σ ∥ Γ ∥ctx 
  ∥-∥mapᵃ {mod = Check} ∅       p = ∥ p ∥⇇
  ∥-∥mapᵃ {mod = Infer} ∅       p = ∥ p ∥⇉
  ∥-∥mapᵃ               (A ∙ Θ) p = ∥-∥mapᵃ Θ p
