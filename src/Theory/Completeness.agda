import Syntax.Simple.Signature  as S
import Syntax.BiTyped.Signature as B

module Theory.Completeness {SD : S.SigD} (BD : B.SigD SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD
open B SD

open import Syntax.BiTyped.Functor     SD
import      Syntax.BiTyped.Pre.Functor SD as P
import      Syntax.Typed.Functor       SD as T

open import Theory.Erasure

open import Syntax.BiTyped.Term      BD
open import Syntax.BiTyped.Pre.Term  BD
open import Syntax.Typed.Term (erase BD)
open import Syntax.Typed.Raw  (erase BD)

private variable
  Ξ : ℕ
  Γ : Cxt 0
  r : Raw _
  d : Mode
  A : Ty

mutual

  completeness : Pre d r  →  Γ ⊢ r ⦂ A  →  Γ ⊢ r [ d ] A
  completeness (` j) (var i eq) = var i eq
  completeness (A ∋ p) (.A ∋ t) = A ∋ completeness p t
  completeness (p ↑)   t        = completeness p t ↑ refl
  completeness (op {rs = i , _} (dep , ps)) (op (σ , σeq , ts)) =
    op (dep , σ , σeq , completenessᵃˢ (BD .ar i .args) ps ts)

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
