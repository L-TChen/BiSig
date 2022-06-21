open import Prelude

import Syntax.Simple.Description       as S
import Syntax.BiTyped.Description as B

module Theory.RawAnnotatability {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open B {SD}

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Tm₀ to T)
open import Syntax.Context

open import Syntax.BiTyped.Raw.Functor       {SD} Id as M
open import Syntax.BiTyped.RawNoMode.Functor {SD} Id as R
open import Syntax.BiTyped.Raw.Term          {SD} Id D
  renaming (Raw to MRaw)
open import Syntax.BiTyped.RawNoMode.Term    {SD} Id D
private variable
  m : Mode
  Ξ : ℕ

mutual
  annotateRaw
    : Raw
    → ∃[ m ] MRaw m
  annotateRaw (` x)   = Infer , (` x)
  annotateRaw (t ⦂ A) with annotateRaw t
  ... | Check , t′ = Infer , (t′ ⦂ A)
  ... | Infer , t′ = Infer , (t′ ↑ ⦂ A)
  annotateRaw (op (D@(ι Infer B Ds) , i , ts)) = Infer , op (D , i , annotateRawⁿ Ds ts)
  annotateRaw (op (D@(ι Check B Ds) , i , ts)) = Check , op (D , i , annotateRawⁿ Ds ts)

  annotateRawⁿ : (Ds : ArgsD Ξ)
    → R.⟦ Ds ⟧ᵃˢ Raw
    → M.⟦ Ds ⟧ᵃˢ MRaw
  annotateRawⁿ ∅        _        = _
  annotateRawⁿ (Θ ⊢[ m ] A ∙ Ds) (t , ts) = annotateRawᵃ Θ m t , annotateRawⁿ Ds ts

  annotateRawᵃ : (Θ : Ctx (TExp Ξ)) (m : Mode)
    → R.⟦ Θ ⟧ᵃ Raw
    → M.⟦ Θ ⟧ᵃ MRaw m
  annotateRawᵃ ∅       m t       with annotateRaw t
  annotateRawᵃ ∅ Check t | Check , t′  = t′
  annotateRawᵃ ∅ Check t | Infer , t′ = t′ ↑
  annotateRawᵃ ∅ Infer t | Check , t′ = t′ ⦂ {!   !} -- in need of a new metavariable
  annotateRawᵃ ∅ Infer t | Infer , t′ = t′
  annotateRawᵃ (A ∙ Θ) m (x , t) = x , annotateRawᵃ Θ m t