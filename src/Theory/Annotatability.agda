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
  open import Syntax.Typed.Intrinsic.Term   TD
  open import Syntax.BiTyped.Intrinsic.Term BD
    renaming (Tm to BTm)

  annotate
    : Tm  A Γ
    → ∃[ m ] BTm m A Γ
  annotate (` x)  = Infer , ` x
  annotate (op (D , i , σ , B=A , ts)) with s i
  ... | ι m B _ , j , refl = m , op (_ , j , refl , σ , B=A , annotateMap _ _ refl ts)

  annotateMap : (D  : T.ArgsD Ξ) (D′ : B.ArgsD Ξ) → eraseᵃˢ D′ ≡ D
    → (T.⟦ D  ⟧ᵃˢ Tm)  σ Γ
    → (B.⟦ D′ ⟧ᵃˢ BTm) σ Γ
  annotateMap ∅        ∅                refl _        = _
  annotateMap (_ ∙ _) (Θ ⊢[ m ] C ∙ Ds) refl (t , ts) =
    annotateMapᵃ Θ m t , annotateMap _ Ds refl ts

  annotateMapᵃ : (Θ : TExps Ξ)
    → (m : Mode)
    → (T.⟦ Θ ⟧ᵃ Tm A)  σ Γ
    → (B.⟦ Θ ⟧ᵃ BTm m A) σ Γ
  annotateMapᵃ ∅       m t with annotate t
  annotateMapᵃ ∅ Check t | Check , t′ = t′
  annotateMapᵃ ∅ Infer t | Check , t′ = _ ∋ t′
  annotateMapᵃ ∅ Check t | Infer , t′ = ⇉ t′ by refl
  annotateMapᵃ ∅ Infer t | Infer , t′ = t′
  annotateMapᵃ (_ ∙ Θ) m t = annotateMapᵃ Θ m t