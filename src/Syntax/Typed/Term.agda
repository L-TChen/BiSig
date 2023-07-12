import Syntax.Simple.Signature as S
import Syntax.Typed.Signature  as T

module Syntax.Typed.Term {SD : S.SigD} (D : T.SigD SD) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.Context           SD
open import Syntax.Typed.Functor     SD
import      Syntax.Typed.Raw.Functor SD as R
open import Syntax.Typed.Raw.Term     D

private variable
  Γ : Cxt 0
  r : Raw _
  A : Ty

infix 6 _⊢_⦂_

data _⊢_⦂_ : Fam₀ Raw where

  var : (i : A ∈ Γ)
      → {j : Fin (length Γ)}
      → L.index i ≡ j
      → --------------------
        Γ ⊢ (` j) ⦂ A

  _∋_ : (A : Ty)
      → Γ ⊢ r ⦂ A
      → ---------------
        Γ ⊢ (A ∋ r) ⦂ A

  op  : {rs : R.⟦ D ⟧ Raw (length Γ)}
      → ⟦ D ⟧ Raw _⊢_⦂_ Γ rs A
      → -----------------------------
        Γ ⊢ op rs ⦂ A
