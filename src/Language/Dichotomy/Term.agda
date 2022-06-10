open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description
module Language.Dichotomy.Term {SD : S.Desc} (D : Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open import Syntax.Context 
open import Syntax.NamedContext Id

open import Syntax.BiTyped.Raw.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term    D Id

open import Syntax.BiTyped.Extrinsic.Functor {SD} D Id as E
open import Syntax.BiTyped.Extrinsic.Term    D    Id

open import Syntax.BiTyped.Intrinsic.Functor {SD}      as I
open import Syntax.BiTyped.Intrinsic.Term    D

open import Language.Dichotomy.Context Id

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
  ∥ ⊢∈ t    ∥⇉ = _ ∋ ∥ t ∥⇇
  ∥ ⊢op t p ∥⇉ = op (∥-∥map _ t p)

  ∥_∥⇇ : Γ ⊢ t ⇇ A → Tm⇇ A ∥ Γ ∥ctx
  ∥ ⊢⇉ t  p ∥⇇ = ⇉ ∥ t ∥⇉ by p
  ∥ ⊢op t p ∥⇇ = op (∥-∥map _ t p)

  ∥-∥map : (D : Desc)
    → (t : (R.⟦ D ⟧ Raw) m)
    → (E.⟦ D ⟧ ⊢⇆) m A Γ        t
    → (I.⟦ D ⟧ Tm) m A ∥ Γ ∥ctx
  ∥-∥map {m = Check} Ds (ι Ξ Check B D , i , t) (σ , B=A , p) =
    ι Ξ Check B D , i , refl , σ , B=A , ∥-∥mapᵃˢ D _ p
  ∥-∥map {m = Infer} Ds (ι Ξ Infer B D , i , t) (σ , B=A , p) =
    ι Ξ Infer B D , i , refl , σ , B=A , ∥-∥mapᵃˢ D _ p

  ∥-∥mapᵃˢ : (D : ArgsD Ξ)
    → (t : (R.⟦ D ⟧ᵃˢ Raw))
    → (E.⟦ D ⟧ᵃˢ ⊢⇆) σ Γ        t
    → (I.⟦ D ⟧ᵃˢ Tm) σ ∥ Γ ∥ctx 
  ∥-∥mapᵃˢ ι        _        _        = tt
  ∥-∥mapᵃˢ (ρ D Ds) (t , ts) (p , ps) = ∥-∥mapᵃ D _ p , ∥-∥mapᵃˢ Ds ts ps

  ∥-∥mapᵃ : (D : ArgD Ξ)
    → (t : (R.⟦ D ⟧ᵃ Raw))
    → (E.⟦ D ⟧ᵃ ⊢⇆) σ Γ        t
    → (I.⟦ D ⟧ᵃ Tm) σ ∥ Γ ∥ctx 
  ∥-∥mapᵃ (ι Check B) _ p = ∥ p ∥⇇
  ∥-∥mapᵃ (ι Infer B) _ p = ∥ p ∥⇉
  ∥-∥mapᵃ (A ∙ D)     _ p = ∥-∥mapᵃ D _ p