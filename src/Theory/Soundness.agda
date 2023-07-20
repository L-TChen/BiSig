import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

module Theory.Soundness {SD : S.SigD} (BD : B.SigD SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD
open B SD

open import Syntax.BiTyped.Functor   SD
import      Syntax.Typed.Functor     SD as T
import      Syntax.Typed.Raw.Functor SD as R

open import Theory.Erasure

open import Syntax.BiTyped.Term          BD
open import Syntax.Typed.Term     (erase BD)
open import Syntax.Typed.Raw.Term (erase BD)

private variable
  Ξ : ℕ
  Γ : Cxt 0
  r : Raw _
  d : Mode
  A : Ty

mutual

  soundness : Γ ⊢ r [ d ] A  →  Γ ⊢ r ⦂ A
  soundness (var i eq) = var i eq
  soundness (A ∋ t)    = A ∋ soundness t
  soundness (t ↑ refl) = soundness t
  soundness (op {rs = i , _} (_ , σ , σ-eq , ts)) =
    op (σ , σ-eq , soundnessᵃˢ (BD .ar i .args) ts)

  soundnessᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)} {σ : TSub Ξ 0}
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ rs
    → T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _⊢_⦂_ σ Γ rs
  soundnessᵃˢ []                  _        = tt
  soundnessᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (t , ts) = soundnessᵃ Δ t , soundnessᵃˢ Ds ts

  soundnessᵃ
    : (Δ : TExps Ξ) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {σ : TSub Ξ 0}
    → ⟦ Δ ⟧ᵃ   Raw (_⊢_[ d ] A) σ Γ r
    → T.⟦ Δ ⟧ᵃ Raw (_⊢_⦂ A)     σ Γ r
  soundnessᵃ []      t = soundness    t
  soundnessᵃ (_ ∷ Δ) t = soundnessᵃ Δ t
