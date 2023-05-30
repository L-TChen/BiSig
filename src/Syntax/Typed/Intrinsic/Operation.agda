{-# OPTIONS --safe #-}

open import Prelude
import Syntax.Simple.Description as S
import Syntax.Typed.Description  as T

module Syntax.Typed.Intrinsic.Operation {SD : S.Desc} {D : T.Desc SD} where
open import Syntax.Simple             SD

open import Syntax.Context            SD

open import Syntax.Typed.Intrinsic.Functor
open import Syntax.Typed.Intrinsic.Term D

private variable
  m n   : ℕ
  σ     : AList n m
  A B   : TExp m
  Γ Δ   : Cxt m

-- mutual
--   _≟_ : (t u : Tm m A Γ) → Dec (t ≡ u)
--   (` x)  ≟ (` y)  with x ≟∈ y
--   ... | yes refl = yes refl
--   ... | no ¬p = no λ where refl → ¬p refl
--   op t ≟ op u with compareMap _ t u
--   ... | yes p = yes (cong op p)
--   ... | no ¬p = no λ where refl → ¬p refl
--   (` _)  ≟ op _ = no λ ()
--   op _ ≟ (` _)  = no λ ()
--
--   compareMap : ∀ D → (t u : (⟦ D ⟧ Tm m) A Γ) → Dec (t ≡ u)
--   compareMap D (_ , i , t) (_ , j , u) with i ≟∈ j
--   ... | no ¬p = no λ where refl → ¬p refl
--   compareMap _ (D , i , t) (_ , _ , u) | yes refl with compareMapᶜ D t u
--   ... | no ¬q = no λ where refl → ¬q refl
--   ... | yes q = yes (cong (λ t → (D , i , t)) q)
--
--   compareMapᶜ : (D : ConD)
--     → (t u : (⟦ D ⟧ᶜ Tm m) A Γ) → Dec (t ≡ u)
--   compareMapᶜ (ι B D) (σ , _ , ts) (σ′ , _ , us) with σ ≟s σ′
--   ... | no ¬p = no λ where refl → ¬p refl
--   compareMapᶜ (ι B D) (σ , refl , ts) (σ′ , refl , us) | yes refl with compareMapᵃˢ D ts us
--   ... | no ¬q = no λ where refl → ¬q refl
--   ... | yes q = yes (cong (λ ts → σ , refl , ts) q)
--
--   compareMapᵃˢ : (D : ArgsD n)
--     → (t u : (⟦ D ⟧ᵃˢ Tm m) σ Γ) → Dec (t ≡ u)
--   compareMapᵃˢ ∅            _        _        = yes refl
--   compareMapᵃˢ (Θ ⊢ C ∙ Ds) (t , ts) (u , us) with compareMapᵃ Θ t u
--   ... | no ¬p = no λ where refl → ¬p refl
--   ... | yes p with compareMapᵃˢ Ds ts us
--   ... | no ¬q = no λ where refl → ¬q refl
--   ... | yes q = yes (cong₂ _,_ p q)
--
--   compareMapᵃ : (Θ : TExps n)
--     → (t u : (⟦ Θ ⟧ᵃ Tm m A) σ Γ) → Dec (t ≡ u)
--   compareMapᵃ ∅       t u = t ≟ u
--   compareMapᵃ (A ∙ Δ) t u = compareMapᵃ Δ t u
