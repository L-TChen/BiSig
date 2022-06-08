open import Prelude
import Syntax.Simple.Description as S
open import Syntax.Typed.Description  as T

module Syntax.Typed.Operation {SD : S.Desc} {D : T.Desc {SD}} where
open import Syntax.Simple.Term SD
  using () renaming (Tm₀ to T; Sub to TSub)
open import Syntax.Simple.Operation as S
  using (_≟s_) renaming (_≟_ to _≟T_)

open import Syntax.Context
  renaming (_≟_ to _≟ᵢ_)

open import Syntax.Typed.Functor
open import Syntax.Typed.Term D

private
  variable
    Ξ     : ℕ
    σ     : TSub Ξ 0
    A B   : T
    Γ Δ   : Ctx T

mutual
  _≟_ : (t u : Tm A Γ) → Dec (t ≡ u)
  (` x)  ≟ (` y)  with x ≟ᵢ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op t ≟ op u with compareMap _ t u
  ... | yes p = yes (cong op p)
  ... | no ¬p = no λ where refl → ¬p refl
  (` _)  ≟ op _ = no λ ()
  op _ ≟ (` _)  = no λ ()

  compareMap : ∀ D → (t u : (⟦ D ⟧ Tm) A Γ) → Dec (t ≡ u)
  compareMap (D ∷ ns) (inl t) (inl u) with compareMapᶜ D t u
  ... | yes p = yes (cong inl p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (_ ∷ ns) (inr t) (inr u) with compareMap ns t u 
  ... | yes p = yes (cong inr p)
  ... | no ¬p = no λ where refl → ¬p refl
  compareMap (n ∷ ns) (inl _) (inr _) = no λ ()
  compareMap (n ∷ ns) (inr _) (inl _) = no λ ()

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
  compareMapᵃ (⊢ B)   t u = t ≟ u
  compareMapᵃ (A ∙ Δ) t u = compareMapᵃ Δ t u