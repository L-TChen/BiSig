{-# OPTIONS --safe #-}

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Completeness {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD
open B SD

open import Syntax.BiTyped.Functor     SD
import      Syntax.BiTyped.Pre.Functor SD as P
import      Syntax.Typed.Functor       SD as T

open import Theory.Erasure.Description

open import Syntax.BiTyped.Term          BD
open import Syntax.BiTyped.Pre.Term      BD
  renaming (Tm to Pre)
open import Syntax.Typed.Term     (erase BD)
open import Syntax.Typed.Raw.Term (erase BD)

private variable
  Ξ : ℕ
  Γ : Cxt₀
  r : Raw _
  d : Mode
  A : TExp₀

mutual

  completeness : Pre d r  →  Γ ⊢ r ⦂ A  →  Γ ⊢ r [ d ] A
  completeness (` ._)  (` i)    = ` i
  completeness (A ∋ p) (.A ∋ t) = A ∋ completeness p t
  completeness (p ↑)   t        = completeness p t ↑ refl
  completeness (op ps) (op ts)  = op (completenessᶜ (BD .rules _) ps ts)

  completenessᶜ
    : (D : ConD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw (length Γ)}
    → P.⟦        D ⟧ᶜ Raw Pre   d   rs
    → T.⟦ eraseᶜ D ⟧ᶜ Raw _⊢_⦂_   Γ rs   A
    →   ⟦        D ⟧ᶜ Raw _⊢_[_]_ Γ rs d A
  completenessᶜ (ι _ _ Ds) (deq , ps) (σ , σeq , ts) =
    deq , σ , σeq , completenessᵃˢ Ds ps ts

  completenessᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)} {σ : TSub Ξ 0}
    → P.⟦         Ds ⟧ᵃˢ Raw Pre         rs
    → T.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw _⊢_⦂_   σ Γ rs
    →   ⟦         Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ rs
  completenessᵃˢ []                  _        _        = tt
  completenessᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (p , ps) (t , ts) =
    completenessᵃ Δ p t , completenessᵃˢ Ds ps ts

  completenessᵃ
    : (Δ : TExps Ξ) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {σ : TSub Ξ 0}
    → P.⟦ Δ ⟧ᵃ Raw Pre                       d     r
    → T.⟦ Δ ⟧ᵃ Raw (λ Γ' r' → Γ' ⊢ r' ⦂ A)     σ Γ r
    →   ⟦ Δ ⟧ᵃ Raw (λ Γ' r' → Γ' ⊢ r' [ d ] A) σ Γ r
  completenessᵃ []      p t = completeness    p t
  completenessᵃ (_ ∷ Δ) p t = completenessᵃ Δ p t
