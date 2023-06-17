open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Term {SD : S.Desc} (Id : Set) (D : B.Desc SD) where

open import Syntax.Simple SD

open import Syntax.NamedContext SD Id

open import Syntax.BiTyped.Extrinsic.Functor SD Id
import      Syntax.BiTyped.Raw.Functor       SD Id   as R
open import Syntax.BiTyped.Raw.Term             Id D

private variable
  Θ Ξ : ℕ
  d   : Mode
  Γ   : Cxt Θ
  x   : Id
  A B : TExp Θ
  t   : Raw Θ d

data ⊢⇆ {Θ : ℕ} : Pred₀ Θ (Raw Θ) where
  ⊢`
    : x ⦂ A ∈ Γ
    → ⊢⇆ Syn A Γ (` x)
  ⊢⦂
    : ⊢⇆ Chk A Γ t
    → ⊢⇆ Syn A Γ (t ⦂ A)
  ⊢↑
    : (eq : A ≡ B)
    → ⊢⇆ Syn B Γ t
    → ⊢⇆ Chk A Γ (t ↑)
  ⊢op
    : (t : R.⟦ D ⟧ (Raw Θ) d)
    → (⊢t : ⟦ D ⟧ ⊢⇆ d A Γ t)
    → ⊢⇆ d A Γ (op t)

infix 6 _⊢_⇒_ _⊢_⇐_

_⊢_⇒_ : Cxt Θ → Raw Θ Syn → TExp Θ → Set
Γ ⊢ t ⇒ A = ⊢⇆ Syn A Γ t

_⊢_⇐_ : Cxt Θ → Raw Θ Chk → TExp Θ → Set
Γ ⊢ t ⇐ A = ⊢⇆ Chk A Γ t
