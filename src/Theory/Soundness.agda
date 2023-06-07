{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Soundness {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD
open B SD

open import Syntax.BiTyped.Functor   SD
import      Syntax.Typed.Functor     SD as T
import      Syntax.Typed.Raw.Functor SD as R

open import Theory.Erasure.Description

open import Syntax.BiTyped.Term          BD
open import Syntax.Typed.Term     (erase BD)
open import Syntax.Typed.Raw.Term (erase BD)

private variable
  Ξ : ℕ
  Γ : Cxt₀
  r : Raw _
  d : Mode
  A : TExp₀

mutual

  soundness : Γ ⊢ r [ d ] A  →  Γ ⊢ r ⦂ A
  soundness (` i)      = ` i
  soundness (A ∋ t)    = A ∋ soundness t
  soundness (t ↑ refl) = soundness t
  soundness (op ts)    = op (soundnessᶜ (BD .rules _) ts)

  soundnessᶜ
    : (D : ConD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw (length Γ)}
    → ⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs d A
    → T.⟦ eraseᶜ D ⟧ᶜ Raw _⊢_⦂_ Γ rs A
  soundnessᶜ (ι _ _ Ds) (_ , σ , σ-eq , ts) = σ , σ-eq , soundnessᵃˢ Ds ts

  soundnessᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)} {σ : TSub Ξ 0}
    → ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ rs
    → T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _⊢_⦂_ σ Γ rs
  soundnessᵃˢ []                  _        = tt
  soundnessᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (t , ts) = soundnessᵃ Δ t , soundnessᵃˢ Ds ts

  soundnessᵃ
    : (Δ : TExps Ξ) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {σ : TSub Ξ 0}
    → ⟦ Δ ⟧ᵃ Raw (λ Γ' r' → Γ' ⊢ r' [ d ] A) σ Γ r
    → T.⟦ Δ ⟧ᵃ Raw (λ Γ' r' → Γ' ⊢ r' ⦂ A) σ Γ r
  soundnessᵃ []      t = soundness    t
  soundnessᵃ (_ ∷ Δ) t = soundnessᵃ Δ t
