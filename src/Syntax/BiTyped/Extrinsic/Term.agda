open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tm₀ to T)

open import Syntax.NamedContext SD Id

open import Syntax.BiTyped.Extrinsic.Functor {SD} Id D
import Syntax.BiTyped.Raw.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term    Id D

private variable
  n m : ℕ
  mod  : Mode
  Γ   : Cxt m
  x   : Id
  A B : TExp m
  t   : Raw m mod

-- ⊢⇄ Infer == _⊢_⇉_
-- ⊢⇄ Check == _⊢_⇇_

data ⊢⇄ {m : ℕ} : Pred₀ m (Raw m) where
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
    : (t : (R.⟦ D ⟧ Raw m) mod)
    → (⊢t : (⟦ D ⟧ ⊢⇄) mod A Γ t)
    → ⊢⇄ mod A Γ (op t)

_⊢_⇉_ : Cxt m → Raw m Infer → TExp m → Set
Γ ⊢ t ⇉ A = ⊢⇄ Infer A Γ t

_⊢_⇇_ : Cxt m → Raw m Check → TExp m → Set
Γ ⊢ t ⇇ A = ⊢⇄ Check A Γ t

