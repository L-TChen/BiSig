import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

module Syntax.BiTyped.Term {SD : S.SigD} (D : B.SigD SD) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.Context           SD
import      Syntax.Typed.Raw.Functor SD as R
open import Syntax.BiTyped.Functor   SD

open import Theory.Erasure
open import Syntax.Typed.Raw.Term (erase D)

private variable
  Γ   : Cxt 0
  r   : Raw _
  d   : Mode
  A B : Ty

infix 6 _⊢_[_]_ _⊢_⇒_ _⊢_⇐_

mutual

  _⊢_⇐_ _⊢_⇒_ : (Γ : Cxt 0) → Raw (length Γ) → Ty → Set
  Γ ⊢ r ⇐ A = Γ ⊢ r [ Chk ] A
  Γ ⊢ r ⇒ A = Γ ⊢ r [ Syn ] A

  data _⊢_[_]_ : Fam₀ Raw where

    var : (i : A ∈ Γ)
        → {j : Fin (length Γ)}
        → L.index i ≡ j
        → --------------------
          Γ ⊢ (` j) ⇒ A

    _∋_ : (A : Ty)
        → Γ ⊢ r ⇐ A
        → Γ ⊢ (A ∋ r) ⇒ A

    _↑_ : Γ ⊢ r ⇒ B
        → A ≡ B
        → ---------
          Γ ⊢ r ⇐ A

    op  : {rs : R.⟦ erase D ⟧ Raw (length Γ)}
        → ⟦ D ⟧ Raw _⊢_[_]_ Γ rs d A
        → -----------------------------------
          Γ ⊢ op rs [ d ] A
