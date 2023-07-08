import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Theory.Pre.TypingErasure {SD : S.Desc} (BD : B.Desc SD) where

open import Prelude

open import Syntax.Simple  SD
open import Syntax.Context SD
open B SD

open import Syntax.BiTyped.Functor     SD
import      Syntax.BiTyped.Pre.Functor SD as P

open import Theory.Erasure

open import Syntax.BiTyped.Term      BD
open import Syntax.BiTyped.Pre.Term  BD
open import Syntax.Typed.Raw  (erase BD)

private variable
  Ξ : ℕ
  Γ : Cxt 0
  r : Raw _
  d : Mode
  A : Ty

mutual

  typingErasure : Γ ⊢ r [ d ] A  →  Pre d r
  typingErasure (var i {j} _) = ` j
  typingErasure (A ∋ t) = A ∋ typingErasure t
  typingErasure (t ↑ _) = (typingErasure t) ↑
  typingErasure (op ts) = op (typingErasureᶜ (BD .rules _) ts)

  typingErasureᶜ
    : (D : ConD) {rs : R.⟦ eraseᶜ D ⟧ᶜ Raw (length Γ)}
    →   ⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs d A
    → P.⟦ D ⟧ᶜ Raw Pre   d   rs
  typingErasureᶜ (ι _ _ Ds) (deq , _ , _ , ts) = deq , typingErasureᵃˢ Ds ts

  typingErasureᵃˢ
    : (Ds : ArgsD Ξ) {rs : R.⟦ eraseᵃˢ Ds ⟧ᵃˢ Raw (length Γ)} {σ : TSub Ξ 0}
    →   ⟦ Ds ⟧ᵃˢ Raw _⊢_[_]_ σ Γ rs
    → P.⟦ Ds ⟧ᵃˢ Raw Pre         rs
  typingErasureᵃˢ []                  _        = tt
  typingErasureᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (t , ts) = typingErasureᵃ Δ t , typingErasureᵃˢ Ds ts

  typingErasureᵃ
    : (Δ : TExps Ξ) {r : R.⟦ Δ ⟧ᵃ Raw (length Γ)} {σ : TSub Ξ 0}
    →   ⟦ Δ ⟧ᵃ Raw (λ Γ' r' → Γ' ⊢ r' [ d ] A) σ Γ r
    → P.⟦ Δ ⟧ᵃ Raw Pre                       d     r
  typingErasureᵃ []      t = typingErasure    t
  typingErasureᵃ (_ ∷ Δ) t = typingErasureᵃ Δ t
