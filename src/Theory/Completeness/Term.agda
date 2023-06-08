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
  
module Raw (Id : Set) (BD : B.Desc) (TD : T.Desc) (s : Completeness BD TD) where mutual
  open import Syntax.Typed.Raw.Functor   SD Id as TF
  open import Syntax.BiTyped.Raw.Functor SD Id as BF

  open import Syntax.Typed.Raw.Term   Id TD
  open import Syntax.BiTyped.Raw.Term Id BD
    renaming (Raw to BiRaw)

  bidirectionalise
    : (t : Raw Θ)
    → Maybe (∃[ d ] BiRaw Θ d)
  bidirectionalise (` x)   = just (_ , ` x)
  bidirectionalise (t ⦂ A) with bidirectionalise t
  ... | nothing       = nothing
  ... | just (Chk , tᵇ) = just (_ , tᵇ ⦂ A)
  ... | just (Syn , tᵇ) = just (_ , tᵇ ↑ ⦂ A)
  bidirectionalise (op (i , ts))  with bidirectionaliseᶜ {D′ = B.rules BD (s i .proj₁)} (s i .proj₂) ts
  ... | nothing = nothing
  ... | just (eq , ts)  = just (_ , op (s i .proj₁ , eq , ts))

  bidirectionaliseᶜ
    : ∀ {D D′} → eraseᶜ D′ ≡ D
    → TF.⟦ D ⟧ᶜ (Raw Θ)
    → Maybe (BF.⟦ D′  ⟧ᶜ (BiRaw Θ) (D′ .ConD.mode))
  bidirectionaliseᶜ refl ts with bidirectionaliseⁿ _ _ refl ts
  ... | nothing  = nothing
  ... | just tsᵇ = just (refl , tsᵇ)

  bidirectionaliseⁿ
    : (D : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → TF.⟦ D ⟧ᵃˢ (Raw Θ)
    → Maybe (BF.⟦ D′ ⟧ᵃˢ (BiRaw Θ))
  bidirectionaliseⁿ []      []                refl _  = just tt 
  bidirectionaliseⁿ (_ ∷ _) (Δ ⊢[ d ] A ∷ Ds) refl (t , ts) with bidirectionaliseᵃ Δ d t
  ... | nothing = nothing 
  ... | just tᵇ with bidirectionaliseⁿ _ Ds refl ts
  ... | nothing  = nothing
  ... | just tsᵇ = just (tᵇ , tsᵇ)

  bidirectionaliseᵃ
    : (Δ : TExps Ξ) (d : Mode)
    → TF.⟦ Δ ⟧ᵃ (Raw Θ)
    → Maybe (BF.⟦ Δ ⟧ᵃ (BiRaw Θ d))
  bidirectionaliseᵃ [] d     t with bidirectionalise t
  ... | nothing = nothing
  -- [TODO] What property does this clause refute? 
  bidirectionaliseᵃ [] Syn t | just (Chk , tᵇ) = nothing
  bidirectionaliseᵃ [] Chk t | just (Chk , tᵇ) = just tᵇ
  bidirectionaliseᵃ [] Chk t | just (Syn , tᵇ) = just (tᵇ ↑)
  bidirectionaliseᵃ [] Syn t | just (Syn , tᵇ) = just tᵇ
  bidirectionaliseᵃ (_ ∷ Δ) d (x , t) with bidirectionaliseᵃ Δ d t
  ... | nothing = nothing
  ... | just tᵇ = just (x , tᵇ)

module Intrinsic (BD : B.Desc) (TD : T.Desc) (s : Completeness BD TD) where mutual
  open import Syntax.Typed.Intrinsic.Functor   as T
  open import Syntax.BiTyped.Intrinsic.Functor as B

  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  bidirectionalise
    :        Tm  Θ   A Γ
    → ∃[ d ] BTm Θ d A Γ
  bidirectionalise (` x)        = Syn , ` x
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
  bidirectionaliseᵃ [] Syn t | Chk , t′ = _ ∋ t′
  bidirectionaliseᵃ [] Chk t | Syn , t′ = t′ ↑by refl
  bidirectionaliseᵃ [] Syn t | Syn , t′ = t′
  bidirectionaliseᵃ (_ ∷ Θ) d t = bidirectionaliseᵃ Θ d t
