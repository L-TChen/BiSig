{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Term {SD : S.Desc} (D : B.Desc SD) where

open import Syntax.Simple            SD
open import Syntax.Context           SD
import      Syntax.Typed.Raw.Functor SD as R
open import Syntax.BiTyped.Functor   SD

open import Theory.Erasure
open import Syntax.Typed.Raw.Term (erase D)

private variable
  Γ   : Cxt₀
  r   : Raw _
  d   : Mode
  A B : TExp₀

infix 6 _⊢_[_]_ _⊢_⇒_ _⊢_⇐_

mutual

  _⊢_⇐_ _⊢_⇒_ : (Γ : Cxt₀) → Raw (length Γ) → TExp₀ → Set
  Γ ⊢ r ⇐ A = Γ ⊢ r [ Chk ] A
  Γ ⊢ r ⇒ A = Γ ⊢ r [ Syn ] A

  data _⊢_[_]_ : Fam₀ Raw where

    `_  : (i : A ∈ Γ)
        → ---------------------
          Γ ⊢ (` L.index i) ⇒ A

    _∋_ : (A : TExp₀)
        → Γ ⊢ r ⇐ A
        → Γ ⊢ (A ∋ r) ⇒ A

    _↑_ : Γ ⊢ r ⇒ A
        → A ≡ B
        → ---------
          Γ ⊢ r ⇐ B

    op  : {rs : R.⟦ erase D ⟧ Raw (length Γ)}
        → ⟦ D ⟧ Raw _⊢_[_]_ Γ rs d A
        → -----------------------------------
          Γ ⊢ op rs [ d ] A
