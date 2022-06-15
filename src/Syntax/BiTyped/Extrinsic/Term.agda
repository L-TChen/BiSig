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
    → ⊢⇄ Infer A Γ (` x)
  ⊢⦂
    : ⊢⇄ Check A Γ t
    → ⊢⇄ Infer A Γ (t ⦂ A)
  ⊢⇉
    : ⊢⇄ Infer A Γ t
    → A ≡ B
    → ⊢⇄ Check B Γ (t ↑)
  ⊢op
    : (t : (R.⟦ D ⟧ Raw) m)
    → (⊢t : (⟦ D ⟧ ⊢⇄) m A Γ t)
    → ⊢⇄ m A Γ (op t)

_⊢_⇉_ : Context T → Raw Infer → T → Set
Γ ⊢ t ⇉ A = ⊢⇄ Infer A Γ t
_⊢_⇇_ : Context T → Raw Check → T → Set
Γ ⊢ t ⇇ A = ⊢⇄ Check A Γ t