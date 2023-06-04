{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Completeness.Term {SD : S.Desc} where

open import Syntax.Simple  SD
open import Syntax.Context SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Theory.Erasure.Description
import Theory.Erasure.Term as E

open import Theory.Completeness.Description SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  ρ   : TSub Ξ Θ
  A B : TExp Ξ
  Γ Δ : Cxt  Θ

module Intrinsic (BD : B.Desc) (TD : T.Desc) (s : Completeness BD TD) where mutual
  open import Syntax.Typed.Intrinsic.Functor   as T
  open import Syntax.BiTyped.Intrinsic.Functor as B

  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  bidirectionalise
    :        Tm  Θ   A Γ
    → ∃[ d ] BTm Θ d A Γ
  bidirectionalise (` x)        = Inf , ` x
  bidirectionalise (op (i , r)) = _ , op (_ , bidirectionaliseᶜ (proj₂ (s i)) r)

  bidirectionaliseᶜ : ∀ {D D′} → eraseᶜ D′ ≡ D
    → T.⟦ D  ⟧ᶜ (Tm Θ) A Γ
    → B.⟦ D′ ⟧ᶜ (BTm Θ) (D′ .ConD.mode) A Γ
  bidirectionaliseᶜ refl (σ , A=B , ts) = refl , σ , A=B , bidirectionaliseⁿ _ _ refl ts

  bidirectionaliseⁿ : (D : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → T.⟦ D  ⟧ᵃˢ (Tm  Θ) ρ Γ
    → B.⟦ D′ ⟧ᵃˢ (BTm Θ) ρ Γ
  bidirectionaliseⁿ []      []                refl _        = _
  bidirectionaliseⁿ (_ ∷ _) (Δ ⊢[ d ] C ∷ Ds) refl (t , ts) =
    bidirectionaliseᵃ Δ d t , bidirectionaliseⁿ _ Ds refl ts

  bidirectionaliseᵃ : (Δ : TExps Ξ)
    → (d : Mode)
    → T.⟦ Δ ⟧ᵃ (Tm  Θ A)   ρ Γ
    → B.⟦ Δ ⟧ᵃ (BTm Θ d A) ρ Γ
  bidirectionaliseᵃ [] d     t with bidirectionalise t
  bidirectionaliseᵃ [] Chk t | Chk , t′ = t′
  bidirectionaliseᵃ [] Inf t | Chk , t′ = _ ∋ t′
  bidirectionaliseᵃ [] Chk t | Inf , t′ = t′ ↑by refl
  bidirectionaliseᵃ [] Inf t | Inf , t′ = t′
  bidirectionaliseᵃ (_ ∷ Θ) d t = bidirectionaliseᵃ Θ d t
