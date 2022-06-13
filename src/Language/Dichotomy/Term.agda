open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description
module Language.Dichotomy.Term {SD : S.Desc} (D : Desc {SD}) (Id : Set) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)
open import Syntax.Context 
open import Syntax.NamedContext Id

open import Syntax.BiTyped.Raw.Functor {SD} Id   as R
open import Syntax.BiTyped.Raw.Term         Id D

open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D as E
open import Syntax.BiTyped.Extrinsic.Term         Id D

open import Syntax.BiTyped.Intrinsic.Functor {SD}      as I
open import Syntax.BiTyped.Intrinsic.Term            D

open import Language.Dichotomy.Context            Id

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
  ∥ ⊢op (ι Ξ Infer B D , i , t) (σ , B=A , p) ∥⇉ =
    op (_ , i , refl , σ , B=A , ∥-∥map D _ p)

  ∥_∥⇇ : Γ ⊢ t ⇇ A → Tm⇇ A ∥ Γ ∥ctx
  ∥ ⊢⇉ t  p ∥⇇ = ⇉ ∥ t ∥⇉ by p
  ∥ ⊢op (ι Ξ Check B D , i , t) (σ , B=A , p) ∥⇇ =
    op (_ , i , refl , σ , B=A , ∥-∥map D _ p)

  ∥-∥map : (D : ArgsD Ξ)
    → (t : (R.⟦ D ⟧ᵃˢ Raw))
    → (E.⟦ D ⟧ᵃˢ ⊢⇄) σ Γ        t
    → (I.⟦ D ⟧ᵃˢ Tm) σ ∥ Γ ∥ctx 
  ∥-∥map ι        _        _        = tt
  ∥-∥map (ρ D Ds) (t , ts) (p , ps) = ∥-∥mapᵃ D _ p , ∥-∥map Ds ts ps

  ∥-∥mapᵃ : (D : ArgD Ξ)
    → (t : (R.⟦ D ⟧ᵃ Raw))
    → (E.⟦ D ⟧ᵃ ⊢⇄) σ Γ        t
    → (I.⟦ D ⟧ᵃ Tm) σ ∥ Γ ∥ctx 
  ∥-∥mapᵃ (ι Check B) _ p = ∥ p ∥⇇
  ∥-∥mapᵃ (ι Infer B) _ p = ∥ p ∥⇉
  ∥-∥mapᵃ (A ∙ D)     _ p = ∥-∥mapᵃ D _ p