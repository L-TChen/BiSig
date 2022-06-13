open import Prelude
import Syntax.Simple.Description as S
open import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Operation {SD : S.Desc} {D : T.Desc {SD}} where
open import Syntax.Simple.Term SD
  using (_≟s_) renaming (Tm₀ to T; Sub to TSub; _≟_ to _≟T_)

open import Syntax.Context

open import Syntax.Typed.Intrinsic.Functor
open import Syntax.Typed.Intrinsic.Term D

open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)

private
  variable
    Ξ     : ℕ
    σ     : TSub Ξ 0
    A B   : T
    Γ Δ   : Ctx T


mutual
  _≟_ : (t u : Tm A Γ) → Dec (t ≡ u)
  (` x)  ≟ (` y)  with x ≟∈ y
  ... | yes refl = yes refl
  ... | no ¬p = no λ where refl → ¬p refl
  op t ≟ op u with compareMap _ t u
  ... | yes p = yes (cong op p)
  ... | no ¬p = no λ where refl → ¬p refl
  (` _)  ≟ op _ = no λ ()
  op _ ≟ (` _)  = no λ ()

  compareMap : ∀ D → (t u : (⟦ D ⟧ Tm) A Γ) → Dec (t ≡ u)
  compareMap D (_ , i , t) (_ , j , u) with i ≟∈ j
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap _ (D , i , t) (_ , _ , u) | yes refl with compareMapᶜ D t u
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ t → (D , i , t)) q)

  compareMapᶜ : (D : ConD) → (t u : (⟦ D ⟧ᶜ Tm) A Γ) → Dec (t ≡ u)
  compareMapᶜ (ι Ξ B D) (σ , _ , ts) (σ′ , _ , us) with σ ≟s σ′
  ... | no ¬p = no λ where refl → ¬p refl
  compareMapᶜ (ι Ξ B D) (σ , refl , ts) (σ′ , refl , us) | yes refl with compareMapᵃˢ D ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ ts → σ , refl , ts) q)

  compareMapᵃˢ : (D : ArgsD Ξ) → (t u : (⟦ D ⟧ᵃˢ Tm) σ Γ) → Dec (t ≡ u)
  compareMapᵃˢ ι        _        _        = yes refl
  compareMapᵃˢ (ρ D Ds) (t , ts) (u , us) with compareMapᵃ D t u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMapᵃˢ Ds ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)

  compareMapᵃ : (D : ArgD Ξ) → (t u : (⟦ D ⟧ᵃ Tm) σ Γ) → Dec (t ≡ u)
  -- compareMapᵃ D t u = t ≟ u
  compareMapᵃ (⊢ B)   t u = t ≟ u
  compareMapᵃ (A ∙ Δ) t u = compareMapᵃ Δ t u