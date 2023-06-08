open import Prelude

import Syntax.Simple.Description  as S
import Syntax.Typed.Description   as T

module Syntax.Typed.Extrinsic.Term {SD : S.Desc} (Id : Set) (D : T.Desc SD) where

open import Syntax.Simple       SD
open import Syntax.NamedContext SD Id

open import Syntax.Typed.Extrinsic.Functor SD Id
import      Syntax.Typed.Raw.Functor       SD Id   as R
open import Syntax.Typed.Raw.Term             Id D

private variable
  Ξ Θ : ℕ
  Γ   : Cxt Θ
  x   : Id
  A B : TExp Ξ
  t   : Raw  Θ

data ⊢ {Θ : ℕ} : Pred₀ Θ (Raw Θ) where
  ⊢`
    : x ⦂ A ∈ Γ
    → ⊢ A Γ (` x)
  ⊢⦂
    : ⊢ B Γ t
    → (eq : A ≡ B)
    → ⊢ A Γ (t ⦂ B)
  ⊢op
    : (t : R.⟦ D ⟧ (Raw Θ))
    → (⊢t : ⟦ D ⟧ ⊢ A Γ t)
    → ⊢ A Γ (op t)

infix 6 _⊢_⦂_

_⊢_⦂_ : Cxt Θ → Raw Θ → TExp Θ → Set
Γ ⊢ t ⦂ A = ⊢ A Γ t
