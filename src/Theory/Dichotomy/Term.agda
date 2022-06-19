open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description

module Theory.Dichotomy.Term {SD : S.Desc} (D : Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T)
open import Syntax.Context
open import Syntax.NamedContext Id

open import Syntax.BiTyped.Raw.Functor {SD} Id   as R
open import Syntax.BiTyped.Raw.Term         Id D

open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D as E
open import Syntax.BiTyped.Extrinsic.Term         Id D

open import Syntax.BiTyped.Intrinsic.Functor {SD}      as I
open import Syntax.BiTyped.Intrinsic.Term            D

open import Theory.Dichotomy.Context            Id

private variable
  m     : Mode
  Ξ     : ℕ
  σ     : Sub₀ Ξ
  A B C : T
  x y   : Id
  Γ     : Context T
  t u   : Raw m

mutual
  ∥_∥⇉ : Γ ⊢ t ⇉ A → Tm⇉ A ∥ Γ ∥ctx
  ∥ ⊢` x    ∥⇉ = ` ∥ x ∥∈
  ∥ ⊢⦂ t    ∥⇉ = _ ∋ ∥ t ∥⇇
  ∥ ⊢op (ι Infer B D , i , t) (σ , B=A , p) ∥⇉ =
    op (_ , i , refl , σ , B=A , ∥-∥map D p)

  ∥_∥⇇ : Γ ⊢ t ⇇ A → Tm⇇ A ∥ Γ ∥ctx
  ∥ ⊢⇉ t  p ∥⇇ = ⇉ ∥ t ∥⇉ by p
  ∥ ⊢op (ι Check B D , i , t) (σ , B=A , p) ∥⇇ =
    op (_ , i , refl , σ , B=A , ∥-∥map D p)

  ∥-∥map : (D : ArgsD Ξ)
    → {t : R.⟦ D ⟧ᵃˢ Raw}
    → (E.⟦ D ⟧ᵃˢ _ , ⊢⇄) σ Γ        t
    → (I.⟦ D ⟧ᵃˢ Tm) σ ∥ Γ ∥ctx 
  ∥-∥map ∅                 _        = tt
  ∥-∥map (Θ ⊢[ m ] B ∙ Ds) (p , ps) = ∥-∥mapᵃ Θ p , ∥-∥map Ds ps

  ∥-∥mapᵃ : (Θ : TExps Ξ)
    → {t : R.⟦ Θ ⟧ᵃ Raw m}
    → (E.⟦ Θ ⟧ᵃ Raw , ⊢⇄ m A) σ Γ        t
    → (I.⟦ Θ ⟧ᵃ Tm m A) σ ∥ Γ ∥ctx 
  ∥-∥mapᵃ {m = Check} ∅       p = ∥ p ∥⇇
  ∥-∥mapᵃ {m = Infer} ∅       p = ∥ p ∥⇉
  ∥-∥mapᵃ             (A ∙ Θ) p = ∥-∥mapᵃ Θ p