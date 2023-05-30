{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description as S

module Theory.Annotatability.Term {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Theory.Erasure.Description
import Theory.Erasure.Term as E

open import Theory.Annotatability.Description SD

private variable
  d   : Mode
  Ξ Θ : ℕ
  ρ   : TSub Ξ Θ
  A B : TExp Ξ
  Γ Δ : Cxt  Θ
  
module Raw (Id : Set) (BD : B.Desc) (TD : T.Desc) (s : Annotatability BD TD) where mutual
  open import Syntax.Typed.Raw.Functor   SD Id as TF
  open import Syntax.BiTyped.Raw.Functor SD Id as BF

  open import Syntax.Typed.Raw.Term   Id TD
  open import Syntax.BiTyped.Raw.Term Id BD
    renaming (Raw to BiRaw)

  annotate
    : (t : Raw Θ)
    → Maybe (∃[ d ] BiRaw Θ d)
  annotate (` x)   = just (_ , ` x)
  annotate (t ⦂ A) with annotate t
  ... | nothing       = nothing
  ... | just (Chk , tᵇ) = just (_ , tᵇ ⦂ A)
  ... | just (Inf , tᵇ) = just (_ , tᵇ ↑ ⦂ A)
  annotate (op (i , ts))  with annotateᶜ {D′ = B.rules BD (s i .proj₁)} (s i .proj₂) ts
  ... | nothing = nothing
  ... | just (eq , ts)  = just (_ , op (s i .proj₁ , eq , ts))

  annotateᶜ
    : ∀ {D D′} → eraseᶜ D′ ≡ D
    → TF.⟦ D ⟧ᶜ (Raw Θ)
    → Maybe (BF.⟦ D′  ⟧ᶜ (BiRaw Θ) (D′ .ConD.mode))
  annotateᶜ refl ts with annotateⁿ _ _ refl ts
  ... | nothing  = nothing
  ... | just tsᵇ = just (refl , tsᵇ)

  annotateⁿ
    : (D : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → TF.⟦ D ⟧ᵃˢ (Raw Θ)
    → Maybe (BF.⟦ D′ ⟧ᵃˢ (BiRaw Θ))
  annotateⁿ []      []                refl _  = just tt 
  annotateⁿ (_ ∷ _) (Δ ⊢[ d ] A ∷ Ds) refl (t , ts) with annotateᵃ Δ d t
  ... | nothing = nothing 
  ... | just tᵇ with annotateⁿ _ Ds refl ts
  ... | nothing  = nothing
  ... | just tsᵇ = just (tᵇ , tsᵇ)

  annotateᵃ
    : (Δ : TExps Ξ) (d : Mode)
    → TF.⟦ Δ ⟧ᵃ (Raw Θ)
    → Maybe (BF.⟦ Δ ⟧ᵃ (BiRaw Θ d))
  annotateᵃ [] d     t with annotate t
  ... | nothing = nothing
  -- [TODO] What property does this clause refute? 
  annotateᵃ [] Inf t | just (Chk , tᵇ) = nothing
  annotateᵃ [] Chk t | just (Chk , tᵇ) = just tᵇ
  annotateᵃ [] Chk t | just (Inf , tᵇ) = just (tᵇ ↑)
  annotateᵃ [] Inf t | just (Inf , tᵇ) = just tᵇ
  annotateᵃ (_ ∷ Δ) d (x , t) with annotateᵃ Δ d t
  ... | nothing = nothing
  ... | just tᵇ = just (x , tᵇ)

module Intrinsic (BD : B.Desc) (TD : T.Desc) (s : Annotatability BD TD) where mutual
  open import Syntax.Typed.Intrinsic.Functor   as T
  open import Syntax.BiTyped.Intrinsic.Functor as B

  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  annotate
    :        Tm  Θ   A Γ
    → ∃[ d ] BTm Θ d A Γ
  annotate (` x)        = Inf , ` x
  annotate (op (i , r)) = _ , op (_ , annotateᶜ (proj₂ (s i)) r)

  annotateᶜ : ∀ {D D′} → eraseᶜ D′ ≡ D
    → T.⟦ D  ⟧ᶜ (Tm Θ) A Γ
    → B.⟦ D′ ⟧ᶜ (BTm Θ) (D′ .ConD.mode) A Γ
  annotateᶜ refl (σ , A=B , ts) = refl , σ , A=B , annotateMap _ _ refl ts

  annotateMap : (D : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → T.⟦ D  ⟧ᵃˢ (Tm  Θ) ρ Γ
    → B.⟦ D′ ⟧ᵃˢ (BTm Θ) ρ Γ
  annotateMap []      []                refl _        = _
  annotateMap (_ ∷ _) (Δ ⊢[ d ] C ∷ Ds) refl (t , ts) =
    annotateMapᵃ Δ d t , annotateMap _ Ds refl ts

  annotateMapᵃ : (Δ : TExps Ξ)
    → (d : Mode)
    → T.⟦ Δ ⟧ᵃ (Tm  Θ A)   ρ Γ
    → B.⟦ Δ ⟧ᵃ (BTm Θ d A) ρ Γ
  annotateMapᵃ [] d     t with annotate t
  annotateMapᵃ [] Chk t | Chk , t′ = t′
  annotateMapᵃ [] Inf t | Chk , t′ = _ ∋ t′
  annotateMapᵃ [] Chk t | Inf , t′ = ⇉ t′ by refl
  annotateMapᵃ [] Inf t | Inf , t′ = t′
  annotateMapᵃ (_ ∷ Θ) d t = annotateMapᵃ Θ d t
