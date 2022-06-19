open import Prelude

import Syntax.Simple.Description as S

module Theory.Annotatability {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T)
open import Syntax.Context

open import Syntax.Typed.Description    {SD} as T
open import Syntax.BiTyped.Description  {SD} as B

open import Syntax.Typed.Intrinsic.Functor    as T
open import Syntax.BiTyped.Intrinsic.Functor  as B

open import Syntax.Typed.Intrinsic.Term
open import Syntax.BiTyped.Intrinsic.Term
  renaming (Tm to BTm)

open import Theory.Erasure.Description

private variable
  m : Mode
  Ξ : ℕ
  A : T
  σ : Sub₀ Ξ
  Γ : Ctx T

-- A bidirectional typing annotates a base typing if every typing rule in the base typing
-- has a corresponding typing rule.
Annotatability : (BD : B.Desc) (TD : T.Desc) → Set
Annotatability BD TD = {D : T.ConD} → D ∈ TD → ∃[ D′ ] (D′ ∈ BD × eraseᶜ D′ ≡ D)

module _ (BD : B.Desc) (TD : T.Desc) (s : Annotatability BD TD) where mutual
  annotate
    : Tm  TD A Γ
    → Tm⇇ BD A Γ
  annotate (` x)  = ⇉ ` x by refl
  annotate (op (D , i , σ , B=A , ts)) with s i
  ... | ι Check B _ , j , refl =   op (_ , j , refl , σ , B=A , annotateMap _ _ refl ts)
  ... | ι Infer B _ , j , refl = ⇉ op (_ , j , refl , σ , B=A , annotateMap _ _ refl ts) by refl

  annotateMap : (D  : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → (T.⟦ D  ⟧ᵃˢ Tm TD)  σ Γ
    → (B.⟦ D′ ⟧ᵃˢ BTm BD) σ Γ
  annotateMap ∅        ∅                refl _        = _
  annotateMap (_ ∙ _) (Θ ⊢[ m ] C ∙ Ds) refl (t , ts) =
    annotateMapᵃ Θ m t , annotateMap _ Ds refl ts

  annotateMapᵃ : (Θ : TExps Ξ)
    → (m : Mode)
    → (T.⟦ Θ ⟧ᵃ Tm TD A)  σ Γ
    → (B.⟦ Θ ⟧ᵃ BTm BD m A) σ Γ
  annotateMapᵃ ∅       Check t = annotate t
  annotateMapᵃ ∅       Infer t = _ ∋ annotate t
  annotateMapᵃ (A ∙ Θ) m     t = annotateMapᵃ Θ m t