open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.NamedContext Id

open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
import Syntax.BiTyped.Raw.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term    Id D

private variable
  Ξ   : ℕ
  m   : Mode
  Γ   : Context T
  x   : Id
  A B : T
  t   : Raw m

data ⊢⇄ : Pred₀ Raw where
  ⊢`
    : x ⦂ A ∈ Γ
    → ⊢⇄ A Γ Infer (` x)
  ⊢⦂
    : ⊢⇄ A Γ Check t
    → ⊢⇄ A Γ Infer (t ⦂ A)
  ⊢⇉
    : ⊢⇄ A Γ Infer t
    → A ≡ B
    → ⊢⇄ B Γ Check (t ↑)
  ⊢op
    : (t : (R.⟦ D ⟧ Raw) m)
    → (⊢t : (⟦ D ⟧ ⊢⇄) m A Γ t)
    → ⊢⇄ A Γ m (op t)

_⊢_⇉_ : Context T → Raw Infer → T → Set
Γ ⊢ t ⇉ A = ⊢⇄ A Γ Infer t
_⊢_⇇_ : Context T → Raw Check → T → Set
Γ ⊢ t ⇇ A = ⊢⇄ A Γ Check t